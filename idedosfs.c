/*
	idedosfs: filesystem for mounting IDEDOS format HDFs
	Copyright (C) 2012 Edward Cree <ec429@cantab.net>

	This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

#define FUSE_USE_VERSION 26

#include <fuse.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>
#include <errno.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/file.h> // for flock()
#include <attr/xattr.h>
#include <pthread.h> // for mutexen

typedef struct
{
	char pn[16]; // partition name
	uint8_t pt; // partition type
	uint16_t sc, ec; // start/end cylinder
	uint8_t sh, eh; // start/end head
	uint32_t ls; // "largest logical sector" (what?)
	char td[0x25]; // type specific data
}
partent;
partent p_decode(const char part[0x40]);

pthread_rwlock_t dmex; // disk mutex
char *dm=NULL; // disk mmap
off_t d_sz; // mmap region size
bool d_8bit; // was disk created with an 8-bit interface?
uint16_t d_nc; // number of cylinders
uint8_t d_nh; // number of heads
uint8_t d_st; // sectors per track
uint32_t d_np; // number of partitions (MP+1)
partent *p_list=NULL;
uint16_t p_dl[256]; // drive letters (0 means not assigned or clash)

#define HDDOFF	(dm[9]|(dm[10]<<8))
#define HSD		(dm[8]&1)
static char bread_havelock(off_t offset); // only call if you already have the lock!!!
static char bread(off_t offset);
static void dread_havelock(char *buf, size_t bytes, off_t offset); // only call if you already have the lock!!!
static void dread(char *buf, size_t bytes, off_t offset);
static void bwrite_havelock(char byte, off_t offset); // only call if you already have the lock!!!
static void bwrite(char byte, off_t offset);
static void dwrite_havelock(const char *buf, size_t bytes, off_t offset); // only call if you already have the lock!!!
static void dwrite(const char *buf, size_t bytes, off_t offset);

static int lookup(const char *path);
static bool islinked(unsigned int p);

#define read16(p)	(((unsigned char *)p)[0]|(((unsigned char *)p)[1]<<8))
#define read32(p)	(((unsigned char *)p)[0]|(((unsigned char *)p)[1]<<8)|(((unsigned char *)p)[2]<<16)|(((unsigned char *)p)[3]<<24))

static int ide_getattr(const char *path, struct stat *st)
{
	memset(st, 0, sizeof(struct stat));
	if(strcmp(path, "/")==0)
	{
		pthread_rwlock_rdlock(&dmex);
		st->st_mode=S_IFDIR | 0400;
		st->st_nlink=4;
		st->st_size=d_sz;
		pthread_rwlock_unlock(&dmex);
		return(0);
	}
	if((strcmp(path, "/by-name")==0)||(strcmp(path, "/by-index")==0))
	{
		st->st_mode=S_IFDIR | 0400;
		st->st_nlink=2;
		return(0);
	}
	int p=lookup(path);
	if((p<0)||(p>=(int)d_np)) return(-ENOENT);
	pthread_rwlock_rdlock(&dmex);
	if(!p_list[p].pt||(p_list[p].pt>0xFD)) // disallow 0 (unused), 0xFE (bad space) and 0xFF (free space)
	{
		pthread_rwlock_unlock(&dmex);
		return(-ENOENT);
	}
	st->st_mode=S_IFREG | 0600;
	st->st_nlink=islinked(p)?3:2;
	st->st_blksize=(d_8bit||HSD)?256:512;
	uint32_t sch=p_list[p].sh+(p_list[p].sc*d_nh), ech=p_list[p].eh+(p_list[p].ec*d_nh); // start and end combined CH
	st->st_size=(ech+1-sch)*d_st*st->st_blksize;
	pthread_rwlock_unlock(&dmex);
	return(0);
}

static int ide_readdir(const char *path, void *buf, fuse_fill_dir_t filler, off_t offset, struct fuse_file_info *fi)
{
	if(strcmp(path, "/")==0)
	{
		filler(buf, ".", NULL, 0);
		filler(buf, "..", NULL, 0);
		filler(buf, "by-name", NULL, 0);
		filler(buf, "by-index", NULL, 0);
		pthread_rwlock_rdlock(&dmex);
		for(unsigned int dl=1;dl<256;dl++)
		{
			if(p_dl[dl])
			{
				char drv[3];
				drv[0]=dl;
				drv[1]=':';
				drv[2]=0;
				filler(buf, drv, NULL, 0);
			}
		}
		pthread_rwlock_unlock(&dmex);
		return(0);
	}
	if(strcmp(path, "/by-name")==0)
	{
		filler(buf, ".", NULL, 0);
		filler(buf, "..", NULL, 0);
		pthread_rwlock_rdlock(&dmex);
		for(unsigned long p=0;p<d_np;p++)
		{
			if(!p_list[p].pt||(p_list[p].pt>0xFD)) continue; // ignore 0 (unused), 0xFE (bad space) and 0xFF (free space)
			char b[17];
			memcpy(b, p_list[p].pn, 16);
			b[16]=0;
			size_t be=15;
			while(be&&(b[be]==' ')) b[be--]=0;
			if(be) filler(buf, b, NULL, 0);
		}
		pthread_rwlock_unlock(&dmex);
		return(0);
	}
	if(strcmp(path, "/by-index")==0)
	{
		filler(buf, ".", NULL, 0);
		filler(buf, "..", NULL, 0);
		pthread_rwlock_rdlock(&dmex);
		for(unsigned long p=0;p<d_np;p++)
		{
			if(!p_list[p].pt||(p_list[p].pt>0xFD)) continue; // ignore 0 (unused), 0xFE (bad space) and 0xFF (free space)
			char b[17];
			snprintf(b, 17, "%lu", p);
			filler(buf, b, NULL, 0);
		}
		pthread_rwlock_unlock(&dmex);
		return(0);
	}
	return(-ENOENT);
}

static int ide_open(const char *path, struct fuse_file_info *fi)
{
	if(fi->flags&O_SYNC) return(-ENOSYS);
	if(fi->flags&O_TRUNC) return(-EACCES);
	int p=lookup(path);
	if((p<0)||(p>=(int)d_np))
	{
		if(fi->flags&O_CREAT)
			return(-EACCES); // you can't create a partition with creat(), because you can't specify its size
		return(-ENOENT);
	}
	pthread_rwlock_rdlock(&dmex);
	if(!p_list[p].pt||(p_list[p].pt>0xFD)) // disallow 0 (unused), 0xFE (bad space) and 0xFF (free space)
	{
		pthread_rwlock_unlock(&dmex);
		if(fi->flags&O_CREAT)
			return(-EACCES); // you can't create a partition with creat(), because you can't specify its size
		return(-ENOENT);
	}
	if((fi->flags&(O_CREAT|O_EXCL))==(O_CREAT|O_EXCL)) return(-EEXIST);
	fi->fh=p;
	pthread_rwlock_unlock(&dmex);
	return(0);
}

static int ide_read(const char *path, char *buf, size_t size, off_t offset, struct fuse_file_info *fi)
{
	int p=fi->fh;
	if((p<0)||(p>=(int)d_np)) return(-EBADF);
	pthread_rwlock_rdlock(&dmex);
	uint32_t sch=p_list[p].sh+(p_list[p].sc*d_nh), ech=p_list[p].eh+(p_list[p].ec*d_nh); // start and end combined CH
	uint16_t bps=(d_8bit||HSD)?256:512;
	size_t len=(ech+1-sch)*d_st*bps;
	if(offset>len) return(0);
	if(size+offset>len) size=len-offset;
	dread_havelock(buf, size, sch*d_st*bps+offset);
	pthread_rwlock_unlock(&dmex);
	return(size);
}

static int ide_write(const char *path, const char *buf, size_t size, off_t offset, struct fuse_file_info *fi)
{
	int p=fi->fh;
	if((p<0)||(p>=(int)d_np)) return(-EBADF);
	pthread_rwlock_wrlock(&dmex);
	uint32_t sch=p_list[p].sh+(p_list[p].sc*d_nh), ech=p_list[p].eh+(p_list[p].ec*d_nh); // start and end combined CH
	uint16_t bps=(d_8bit||HSD)?256:512;
	size_t len=(ech+1-sch)*d_st*bps;
	if(size+offset>len) return(-ENOSPC);
	dwrite_havelock(buf, size, sch*d_st*bps+offset);
	pthread_rwlock_unlock(&dmex);
	return(size);
}

static int ide_truncate(const char *path, off_t offset)
{
	return(0); // do nothing, because you can't truncate partitions!
}

static int ide_getxattr(const char *path, const char *name, char *value, size_t vlen)
{
	int p=lookup(path);
	if((p<0)||(p>=(int)d_np)) return(-ENOATTR);
	pthread_rwlock_rdlock(&dmex);
	if(!p_list[p].pt||(p_list[p].pt>0xFD)) // disallow 0 (unused), 0xFE (bad space) and 0xFF (free space)
	{
		pthread_rwlock_unlock(&dmex);
		return(-ENOENT);
	}
	if(strcmp(name, "user.idedos.pt")==0)
	{
		int rlen=4; // 4 bytes will always be enough as max value is "255"
		if(value)
			snprintf(value, vlen, "%u%n", p_list[p].pt, &rlen);
		pthread_rwlock_unlock(&dmex);
		return(rlen);
	}
	if(p_list[p].pt==3)
	{
		if(strcmp(name, "user.plus3dos.xdpb.ndirent")==0)
		{
			unsigned int nd=read16(p_list[p].td+12)+1;
			int rlen=6; // 6 bytes will always be enough as max value is "65536"
			if(value)
				snprintf(value, vlen, "%u%n", nd, &rlen);
			pthread_rwlock_unlock(&dmex);
			return(rlen);
		}
		if(strcmp(name, "user.plus3dos.xdpb.nblocks")==0)
		{
			unsigned int nd=read16(p_list[p].td+10)+1;
			int rlen=6; // 6 bytes will always be enough as max value is "65536"
			if(value)
				snprintf(value, vlen, "%u%n", nd, &rlen);
			pthread_rwlock_unlock(&dmex);
			return(rlen);
		}
		if(strcmp(name, "user.plus3dos.xdpb.bsh")==0)
		{
			uint8_t bsh=p_list[p].td[7];
			int rlen=4; // 4 bytes will always be enough as max value is "256"
			if(value)
				snprintf(value, vlen, "%u%n", bsh, &rlen);
			pthread_rwlock_unlock(&dmex);
			return(rlen);
		}
	}
	pthread_rwlock_unlock(&dmex);
	return(-ENOATTR);
}

static int ide_listxattr(const char *path, char *list, size_t size)
{
	int p=lookup(path);
	if((p<0)||(p>=(int)d_np)) return(-ENOATTR);
	pthread_rwlock_rdlock(&dmex);
	if(!p_list[p].pt||(p_list[p].pt>0xFD)) // disallow 0 (unused), 0xFE (bad space) and 0xFF (free space)
	{
		pthread_rwlock_unlock(&dmex);
		return(-ENOENT);
	}
	size_t nxattrs=0;
	const char *xattrs[256];
	xattrs[nxattrs++]="user.idedos.pt";
	if(p_list[p].pt==3)
	{
		xattrs[nxattrs++]="user.plus3dos.xdpb.ndirent";
		xattrs[nxattrs++]="user.plus3dos.xdpb.nblocks";
		xattrs[nxattrs++]="user.plus3dos.xdpb.bsh";
	}
	size_t listsize=0;
	for(size_t i=0;i<nxattrs;i++)
		listsize+=strlen(xattrs[i])+1;
	if(size)
	{
		if(size<listsize)
		{
			pthread_rwlock_unlock(&dmex);
			return(-ERANGE);
		}
		for(size_t i=0;i<nxattrs;i++)
		{
			size_t l=strlen(xattrs[i]);
			strcpy(list, xattrs[i]);
			list[l]=0;
			list+=l+1;
		}
	}
	pthread_rwlock_unlock(&dmex);
	return(listsize);
}

static struct fuse_operations ide_oper = {
	.getattr	= ide_getattr,
	/*.access		= ide_access,
	.readlink	= ide_readlink,*/
	.readdir	= ide_readdir,
	/*.mknod		= ide_mknod,
	.mkdir		= ide_mkdir,
	.symlink	= ide_symlink,
	.unlink		= ide_unlink,
	.rmdir		= ide_rmdir,
	.rename		= ide_rename,
	.link		= ide_link,
	.chmod		= ide_chmod,
	.chown		= ide_chown,*/
	.truncate	= ide_truncate,
	/*.utimens	= ide_utimens,*/
	.open		= ide_open,
	.read		= ide_read,
	.write		= ide_write,
	/*.statfs		= ide_statfs,
	.release	= ide_release,
	.fsync		= ide_fsync,*/
	/*.setxattr	= ide_setxattr,*/
	.getxattr	= ide_getxattr,
	.listxattr	= ide_listxattr,
	/*.removexattr= ide_removexattr,*/
};

int main(int argc, char *argv[])
{
	if(argc<3)
	{
		fprintf(stderr, "Usage: idedosfs <hdf-image> <mountpoint> [options]\n");
		return(1);
	}
	if(pthread_rwlock_init(&dmex, NULL))
	{
		perror("idedosfs: pthread_rwlock_init");
		return(1);
	}
	const char *hdf=argv[1];
	struct stat st;
	if(stat(hdf, &st))
	{
		fprintf(stderr, "idedosfs: Failed to stat '%s'\n", hdf);
		perror("\tstat");
		pthread_rwlock_destroy(&dmex);
		return(1);
	}
	d_sz=st.st_size;
	fprintf(stderr, "idedosfs: '%s' size is %jdB", hdf, (intmax_t)d_sz);
	if(d_sz>2048)
	{
		const char *u="k";
		size_t uf=1024;
		if(d_sz/uf>2048)
		{
			u="M";
			uf*=1024;
		}
		if(d_sz/uf>2048)
		{
			u="G";
			uf*=1024;
		}
		fprintf(stderr, " (%.3g%sB)", d_sz/(double)uf, u);
	}
	fprintf(stderr, "\n");
	int dfd=open(hdf, O_RDWR);
	if(dfd<0)
	{
		perror("idedosfs: open");
		pthread_rwlock_destroy(&dmex);
		return(1);
	}
	if(flock(dfd, LOCK_EX|LOCK_NB))
	{
		if(errno==EWOULDBLOCK)
		{
			fprintf(stderr, "idedosfs: '%s' is locked by another process (flock: EWOULDBLOCK)\n", hdf);
		}
		else
			perror("idedosfs: flock");
		pthread_rwlock_destroy(&dmex);
		return(1);
	}
	dm=mmap(NULL, d_sz, PROT_READ|PROT_WRITE, MAP_SHARED|MAP_POPULATE, dfd, 0);
	if(!dm)
	{
		perror("idedosfs: mmap");
		flock(dfd, LOCK_UN);
		close(dfd);
		pthread_rwlock_destroy(&dmex);
		return(1);
	}
	fprintf(stderr, "idedosfs: '%s' mmap()ed in\n", hdf);
	int rv=EXIT_FAILURE;
	if(memcmp(dm, "RS-IDE\032", 7))
	{
		fprintf(stderr, "idedosfs: '%s' is not a valid HDF file\n", hdf);
		goto shutdown;
	}
	if(dm[7]!=0x11)
	{
		fprintf(stderr, "idedosfs: '%s' is not a version 1.1 HDF file.\n\tOnly version 1.1 files are supported.\n", hdf);
		goto shutdown;
	}
	pthread_rwlock_wrlock(&dmex);
	fprintf(stderr, "idedosfs: HDDOFF = %04x%s\n", HDDOFF, HSD?", HSD":"");
	d_8bit=false;
	char syspart[0x40];
	dread_havelock(syspart, 0x40, 0);
	partent sp=p_decode(syspart);
	if((!HSD)&&memcmp(sp.pn, "PLUSIDEDOS      ", 16))
	{
		fprintf(stderr, "idedosfs: sp.pn = %.16s\nTrying d_8bit...\n", sp.pn);
		d_8bit=true;
		dread_havelock(syspart, 0x40, 0);
		sp=p_decode(syspart);
	}
	pthread_rwlock_unlock(&dmex);
	if(memcmp(sp.pn, "PLUSIDEDOS      ", 16))
	{
		fprintf(stderr, "idedosfs: '%s' is not formatted\n\tno PLUSIDEDOS system partition!\n", hdf);
		fprintf(stderr, "idedosfs: sp.pn = %.16s\n", sp.pn);
		goto shutdown;
	}
	pthread_rwlock_rdlock(&dmex);
	if(d_8bit)
		fprintf(stderr, "idedosfs: 8bit disk detected\n");
	pthread_rwlock_unlock(&dmex);
	if(sp.pt!=0x01)
	{
		fprintf(stderr, "idedosfs: '%s' is not formatted\n\tsp.pt = 0x%02x != 0x01\n", hdf, sp.pt);
		goto shutdown;
	}
	if(sp.sc)
	{
		fprintf(stderr, "idedosfs: '%s' is not formatted\n\tsp.sc = 0x%04x != 0x0000\n", hdf, sp.sc);
		goto shutdown;
	}
	pthread_rwlock_wrlock(&dmex);
	d_nc=read16(sp.td+0x5);
	d_nh=sp.td[0x7];
	d_st=sp.td[0x8];
	d_np=read16(sp.td+0x0B)+1;
	if(!(p_list=malloc(d_np*sizeof(partent))))
	{
		perror("idedosfs: malloc");
		pthread_rwlock_unlock(&dmex);
		goto shutdown;
	}
	p_list[0]=sp;
	bool dlclash[256];
	memset(dlclash, 0, sizeof(dlclash));
	for(size_t i=1;i<d_np;i++)
	{
		char part[0x40];
		dread_havelock(part, 0x40, i*0x40);
		p_list[i]=p_decode(part);
		switch(p_list[i].pt)
		{
			case 0:
				fprintf(stderr, "idedosfs: partent %04x: unused\n", i);
			break;
			case 0xfe:
				fprintf(stderr, "idedosfs: partent %04x: bad space\n", i);
			break;
			case 0xff:
				fprintf(stderr, "idedosfs: partent %04x: free space\n", i);
			break;
			case 3: // +3DOS
			{
				uint8_t dl=p_list[i].td[0x21];
				if(!dlclash[dl])
				{
					if(p_dl[dl])
					{
						p_dl[dl]=0;
						dlclash[dl]=true;
					}
					else
						p_dl[dl]=i;
				}
			}
			/* fallthrough */
			default:
				fprintf(stderr, "idedosfs: partent %04x: type %02x, name '%.16s'\n", i, p_list[i].pt, p_list[i].pn);
		}
	}
	pthread_rwlock_unlock(&dmex);
	
	int fargc=argc-1;
	char **fargv=(char **)malloc(fargc*sizeof(char *));
	fargv[0]=argv[0];
	for(int i=1;i<fargc;i++)
		fargv[i]=argv[i+1];
	
	rv=fuse_main(fargc, fargv, &ide_oper, NULL);
	shutdown:
	pthread_rwlock_wrlock(&dmex);
	munmap(dm, d_sz);
	flock(dfd, LOCK_UN);
	close(dfd);
	pthread_rwlock_unlock(&dmex);
	pthread_rwlock_destroy(&dmex);
	return(rv);
}

char bread_havelock(off_t offset)
{
	if(offset<d_sz)
		return(dm[offset]);
	return(0);
}

char bread(off_t offset)
{
	pthread_rwlock_rdlock(&dmex);
	char rv=bread_havelock(offset);
	pthread_rwlock_unlock(&dmex);
	return(rv);
}

void dread_havelock(char *buf, size_t bytes, off_t offset)
{
	if(!buf) return;
	if(d_8bit&&!HSD)
		for(size_t i=0;i<bytes;i++)
			buf[i]=bread_havelock(HDDOFF+((offset+i)<<1));
	else
		memcpy(buf, dm+HDDOFF+offset, bytes);
}

void dread(char *buf, size_t bytes, off_t offset)
{
	if(!buf) return;
	pthread_rwlock_rdlock(&dmex);
	dread_havelock(buf, bytes, offset);
	pthread_rwlock_unlock(&dmex);
}

static void bwrite_havelock(char byte, off_t offset)
{
	if(offset<d_sz)
		dm[offset]=byte;
}

static void bwrite(char byte, off_t offset)
{
	pthread_rwlock_wrlock(&dmex);
	bwrite_havelock(byte, offset);
	pthread_rwlock_unlock(&dmex);
}

static void dwrite_havelock(const char *buf, size_t bytes, off_t offset)
{
	if(!buf) return;
	if(d_8bit&&!HSD)
		for(size_t i=0;i<bytes;i++)
		{
			bwrite_havelock(buf[i], HDDOFF+((offset+i)<<1));
			bwrite_havelock(0, HDDOFF+((offset+i)<<1)+1);
		}
	else
		memcpy(dm+HDDOFF+offset, buf, bytes);
}

static void dwrite(const char *buf, size_t bytes, off_t offset)
{
	if(!buf) return;
	pthread_rwlock_wrlock(&dmex);
	dwrite_havelock(buf, bytes, offset);
	pthread_rwlock_unlock(&dmex);
}

partent p_decode(const char part[0x40])
{
	/* syspart.  Others will have different TD after the last LS
			x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 xA xB xC xD xE xF
	0x0000	PN PN PN PN PN PN PN PN PN PN PN PN PN PN PN PN
	0x0010	PT SC SC SH EC EC EH LS LS LS LS 00 00 00 00 00
	0x0020	NC NC NH ST SC SC MP MP EA BA UA UB UM M0 M1 MR
	0x0030	DD 00 00 00 00 00 00 00 00 00 00 00 00 00 00 00
	*/
	partent rv;
	memcpy(rv.pn, part, 0x10);
	rv.pt=part[0x10];
	rv.sc=read16(part+0x11);
	rv.sh=part[0x13];
	rv.ec=read16(part+0x14);
	rv.eh=part[0x16];
	rv.ls=read32(part+0x17);
	memcpy(rv.td, part+0x1B, 0x25);
	return(rv);
}

static int lookup(const char *path)
{
	if(strncmp(path, "/by-name/", 9)==0)
	{
		pthread_rwlock_rdlock(&dmex);
		char spath[16];
		bool nul=false;
		for(size_t i=0;i<16;i++)
		{
			spath[i]=' ';
			if(nul) continue;
			else if(path[i+9])
				spath[i]=path[i+9];
			else
				nul=true;
		}
		for(unsigned long p=0;p<d_np;p++)
		{
			if(!memcmp(p_list[p].pn, spath, 16))
			{
				pthread_rwlock_unlock(&dmex);
				return(p);
			}
		}
		pthread_rwlock_unlock(&dmex);
		return(-1);
	}
	if(strncmp(path, "/by-index/", 10)==0)
	{
		unsigned int p;
		ssize_t b;
		if(sscanf(path+10, "%u%zn", &p, &b)==1)
		{
			if(path[10+b]) return(-ENOENT);
			pthread_rwlock_rdlock(&dmex);
			if(p<d_np)
			{
				pthread_rwlock_unlock(&dmex);
				return(p);
			}
			pthread_rwlock_unlock(&dmex);
		}
		return(-1);
	}
	if((path[0]=='/')&&path[1]&&!strcmp(path+2, ":"))
	{
		uint8_t dl=path[1];
		pthread_rwlock_rdlock(&dmex);
		if(p_dl[dl])
		{
			pthread_rwlock_unlock(&dmex);
			return(p_dl[dl]);
		}
		pthread_rwlock_unlock(&dmex);
		return(-1);
	}
	return(-1);
}

static bool islinked(unsigned int p)
{
	bool linked=false;
	pthread_rwlock_rdlock(&dmex);
	if(p_list[p].pt==0x03)
	{
		uint8_t dl=p_list[p].td[0x21];
		linked=p&&(p_dl[dl]==p);
	}
	pthread_rwlock_unlock(&dmex);
	return(linked);
}
