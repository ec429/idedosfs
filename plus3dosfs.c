/*
	plus3dosfs: filesystem for mounting +3DOS partitions from an idedosfs
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
	uint8_t status;
	char name[8];
	char ext[3];
	bool ro,sys,ar;
	uint16_t xnum; // extent number
	uint8_t rcount; // count of records in last used logical extent
	uint8_t bcount; // count of bytes in last used record.  +3DOS apparently doesn't use this (so you have to rely on the header)
	/*
		Files without headers can
		only record their EOF position to the start of the next 128 byte
		record, i.e. ceiling(EOF/128). Files with headers have their EOF
		position recorded exactly.
		-- The Sinclair ZX Spectrum +3 manual, Chapter 8, Part 27: "Guide to +3DOS"
	*/
	uint16_t al[16]; // block pointers
}
plus3_dirent;

pthread_rwlock_t dmex; // disk mutex
char *dm=NULL; // disk mmap
off_t d_sz; // mmap region size
uint32_t d_ndirent; // number of directory entries (DRM+1)
uint32_t d_nblocks; // number of blocks (DSM+1)
uint8_t d_bsh; // BSH (Block SHift)
bool d_manyblocks; // if true, there are only 8 block pointers in a dirent as each block pointer is 2 bytes
plus3_dirent *d_list=NULL;
bool *d_bitmap=NULL; // disk block map, true if in use

static void dread(char *buf, size_t bytes, off_t offset);
static void dwrite(char *src, size_t bytes, off_t offset);
static plus3_dirent d_decode(const char buf[0x20]);
static void d_encode(char buf[0x20], plus3_dirent src);
static int32_t lookup(const char *path);
static int32_t lookup_extent(const char *path, uint16_t extent);
static uint16_t disk_alloc(void); // allocates a block.  Make sure you have wrlock before calling!
static int32_t extent_alloc(plus3_dirent last, uint16_t extent); // allocates and populates a dirent.  Make sure you have wrlock before calling!

static int plus3_write(const char *path, const char *buf, size_t size, off_t offset, struct fuse_file_info *fi);

static uint16_t read16(const char *p)
{
	return(
		((unsigned char *)p)[0]
		|(((unsigned char *)p)[1]<<8)
	);
}

static uint32_t read32(const char *p)
{
	return(
		((const unsigned char *)p)[0]
		|(((const unsigned char *)p)[1]<<8)
		|(((const unsigned char *)p)[2]<<16)
		|(((const unsigned char *)p)[3]<<24)
	);
}

static void write16(char *p, uint16_t v)
{
	((unsigned char *)p)[0]=(uint8_t)v;
	((unsigned char *)p)[1]=(uint8_t)(v>>8);
}

static void write32(char *p, uint16_t v)
{
	((unsigned char *)p)[0]=(uint8_t)v;
	((unsigned char *)p)[1]=(uint8_t)(v>>8);
	((unsigned char *)p)[2]=(uint8_t)(v>>16);
	((unsigned char *)p)[3]=(uint8_t)(v>>24);
}

static int plus3_getattr(const char *path, struct stat *st)
{
	memset(st, 0, sizeof(struct stat));
	if(strcmp(path, "/")==0)
	{
		st->st_mode=S_IFDIR | 0400;
		st->st_nlink=2;
		st->st_size=d_sz;
		return(0);
	}
	if(path[0]!='/') return(-ENOENT);
	int32_t i=lookup(path);
	if((i<0)||(i>=(int32_t)d_ndirent))
		return(-ENOENT);
	pthread_rwlock_rdlock(&dmex);
	st->st_mode=S_IFREG | (d_list[i].ro?0500:0700);
	st->st_size=128*d_list[i].rcount+d_list[i].bcount;
	// grovel for the header
	off_t where=(((off_t)d_list[i].al[0])<<(7+d_bsh));
	if(memcmp(dm+where, "PLUS3DOS\032", 9)==0)
	{
		uint32_t size=read32(dm+where+11);
		uint8_t ck=0; // header checksum
		for(size_t i=0;i<127;i++)
			ck+=dm[where+i];
		if(ck==(uint8_t)dm[where+127])
			st->st_size=size-128; // first 128 bytes are the header itself
	}
	/*else
		fprintf(stderr, "plus3dosfs: NOHEADER\n");*/
	st->st_nlink=1;
	pthread_rwlock_unlock(&dmex);
	return(0);
}

static int plus3_readdir(const char *path, void *buf, fuse_fill_dir_t filler, off_t offset, struct fuse_file_info *fi)
{
	if(strcmp(path, "/")==0)
	{
		filler(buf, ".", NULL, 0);
		filler(buf, "..", NULL, 0);
		pthread_rwlock_rdlock(&dmex);
		for(uint32_t i=0;i<d_ndirent;i++)
		{
			if((d_list[i].status<16)&&!d_list[i].xnum)
			{
				char nm[13];
				char ex[4];
				memcpy(nm, d_list[i].name, 8);
				memcpy(ex, d_list[i].ext, 3);
				size_t ne=8, ee=3;
				nm[ne]=ex[ee]=0;
				while(ne&&(nm[ne-1]==' ')) nm[--ne]=0;
				while(ee&&(ex[ee-1]==' ')) ex[--ee]=0;
				if(!(ne||ee)) continue;
				if(ee) snprintf(nm+ne, 13-ne, ".%s", ex);
				filler(buf, nm, NULL, 0);
			}
		}
		pthread_rwlock_unlock(&dmex);
		return(0);
	}
	return(-ENOENT);
}

static int plus3_open(const char *path, struct fuse_file_info *fi)
{
	if(fi->flags&O_SYNC) return(-ENOSYS);
	if(fi->flags&O_TRUNC) return(-EACCES);
	if(strcmp(path, "/")==0)
	{
		return(-EISDIR);
	}
	if(path[0]!='/') return(-ENOENT);
	int32_t i=lookup(path);
	if((i<0)||(i>=(int32_t)d_ndirent))
	{
		if(fi->flags&O_CREAT)
			return(-ENOSYS);
		return(-ENOENT);
	}
	if((fi->flags&O_CREAT)&&(fi->flags&O_EXCL)) return(-EEXIST);
	fi->fh=i;
	return(0);
}

static int plus3_create(const char *path, mode_t mode, struct fuse_file_info *fi)
{
	if(fi->flags&O_SYNC) return(-ENOSYS);
	if(strcmp(path, "/")==0)
		return(-EISDIR);
	if(path[0]!='/') return(-ENOENT);
	int32_t i=lookup(path);
	if((i<0)||(i>=(int32_t)d_ndirent))
	{
		path++;
		char nm[8], ex[3];
		size_t ne,nl,ee=0;
		for(ne=0;ne<8;ne++)
		{
			if(path[ne]=='.') break;
			if(!path[ne]) break;
			nm[ne]=path[ne];
		}
		nl=ne;
		for(;ne<8;ne++)
			nm[ne]=' ';
		if(path[nl])
		{
			if(path[nl++]!='.') return(-ENOENT);
			for(;ee<3;ee++)
			{
				if(!path[nl+ee]) break;
				ex[ee]=path[nl+ee];
			}
		}
		for(;ee<3;ee++)
			ex[ee]=' ';
		plus3_dirent last;
		last.status=0;
		memcpy(last.name, nm, 8);
		memcpy(last.ext, ex, 3);
		last.ro=last.sys=last.ar=false;
		pthread_rwlock_wrlock(&dmex);
		i=extent_alloc(last, 0);
		pthread_rwlock_unlock(&dmex);
		if(i>=0)
		{
			fi->fh=i;
			char hbuf[128];
			memset(hbuf, 0, 128);
			memcpy(hbuf, "PLUS3DOS\32\1\0\200\0\0\0\377", 16);
			uint8_t ck=0; // header checksum
			for(size_t i=0;i<127;i++)
				ck+=hbuf[i];
			hbuf[127]=ck;
			pthread_rwlock_wrlock(&dmex);
			if((d_list[i].al[0]=disk_alloc()))
			{
				d_list[i].rcount=1<<d_bsh;
				off_t where=(((off_t)d_list[i].al[0])<<(7+d_bsh));
				memcpy(dm+where, hbuf, 128);
			}
			d_encode(dm+i*0x20, d_list[i]);
			pthread_rwlock_unlock(&dmex);
			return(0);
		}
		return(-ENOSPC);
	}
	return(-EEXIST);
}

static int plus3_unlink(const char *path)
{
	if(strcmp(path, "/")==0)
	{
		return(-EISDIR);
	}
	if(path[0]!='/') return(-ENOENT);
	int32_t i=lookup(path);
	if((i<0)||(i>=(int32_t)d_ndirent))
		return(-ENOENT);
	path++;
	char nm[9], ex[4];
	size_t ne,nl,ee=0;
	for(ne=0;ne<8;ne++)
	{
		if(path[ne]=='.') break;
		if(!path[ne]) break;
		nm[ne]=path[ne];
	}
	nl=ne;
	for(;ne<8;ne++)
		nm[ne]=' ';
	nm[8]=0;
	if(path[nl])
	{
		if(path[nl++]!='.') return(-1);
		for(;ee<3;ee++)
		{
			if(!path[nl+ee]) break;
			ex[ee]=path[nl+ee];
		}
	}
	for(;ee<3;ee++)
		ex[ee]=' ';
	ex[3]=0;
	pthread_rwlock_wrlock(&dmex);
	for(uint32_t i=0;i<d_ndirent;i++)
	{
		if(d_list[i].status<16)
		{
			if(!memcmp(nm, d_list[i].name, 8))
				if(!memcmp(ex, d_list[i].ext, 3))
				{
					for(unsigned int b=0;b<(d_manyblocks?8:16);b++)
					{
						if(d_list[i].al[b])
							d_bitmap[d_list[i].al[b]]=false;
						d_list[i].al[b]=0;
					}
					d_list[i].status=0xe5;
					d_encode(dm+i*0x20, d_list[i]);
				}
		}
	}
	pthread_rwlock_unlock(&dmex);
	return(0);
}

static int plus3_read(const char *path, char *buf, size_t size, off_t offset, struct fuse_file_info *fi)
{
	int32_t i=fi->fh;
	if((i<0)||(i>=(int32_t)d_ndirent))
		return(-ENOENT);
	pthread_rwlock_rdlock(&dmex);
	// grovel for the header
	off_t where=(((off_t)d_list[i].al[0])<<(7+d_bsh));
	if(memcmp(dm+where, "PLUS3DOS\032", 9)==0)
	{
		uint32_t size=read32(dm+where+11);
		uint8_t ck=0; // header checksum
		for(size_t i=0;i<127;i++)
			ck+=dm[where+i];
		if(ck==(uint8_t)dm[where+127])
			offset+=128;
	}
	uint32_t blocknum=offset>>(7+d_bsh), endblocknum=(offset+size-1)>>(7+d_bsh);
	uint32_t transferred=0, len=1<<(7+d_bsh);
	for(uint32_t b=blocknum;b<=endblocknum;b++)
	{
		if(b%(d_manyblocks?8:16))
		{
			if(i>=0)
			{
				if(d_list[i].al[b%(d_manyblocks?8:16)])
					where=(((off_t)d_list[i].al[b%(d_manyblocks?8:16)])<<(7+d_bsh));
				else
					where=0;
			}
		}
		else if(b)
		{
			uint16_t extent=b/(d_manyblocks?8:16);
			i=lookup_extent(path, extent);
			if(i>=0)
			{
				if(d_list[i].al[0])
					where=(((off_t)d_list[i].al[0])<<(7+d_bsh));
				else
					where=0;
			}
		}
		if(transferred+len>size)
			len=size-transferred;
		if((i>=0)&&where)
			memcpy(buf+transferred, dm+where+(offset+transferred)%(1<<(7+d_bsh)), len);
		else
			memset(buf+transferred, 0, len);
		transferred+=len;
	}
	size=transferred;
	pthread_rwlock_unlock(&dmex);
	return(size);
}

static int plus3_write(const char *path, const char *buf, size_t size, off_t offset, struct fuse_file_info *fi)
{
	int32_t i=fi->fh;
	if((i<0)||(i>=(int32_t)d_ndirent))
		return(-ENOENT);
	pthread_rwlock_wrlock(&dmex);
	// grovel for the header
	bool noblocks=!d_list[i].al[0];
	off_t where=0;
	if(!noblocks)
	{
		where=(((off_t)d_list[i].al[0])<<(7+d_bsh));
		if(memcmp(dm+where, "PLUS3DOS\032", 9)==0)
		{
			uint32_t hsize=read32(dm+where+11);
			fprintf(stderr, "hsize = %zu\n", (size_t)hsize);
			uint8_t ck=0; // header checksum
			for(size_t i=0;i<127;i++)
				ck+=dm[where+i];
			if(ck==(uint8_t)dm[where+127])
			{
				offset+=128;
				if(offset+size>hsize)
				{
					fprintf(stderr, "Extended file to length %zu\n", (size_t)(offset+size));
					write32(dm+where+11, (size_t)(offset+size));
					write16(dm+where+16, (size_t)(offset+size-128));
				}
				ck=0;
				for(size_t i=0;i<127;i++)
					ck+=dm[where+i];
				dm[where+127]=ck;
			}
		}
	}
	uint32_t blocknum=offset>>(7+d_bsh), endblocknum=(offset+size-1)>>(7+d_bsh);
	uint16_t extent=blocknum/(d_manyblocks?8:16);
	plus3_dirent last=d_list[i];
	pthread_rwlock_unlock(&dmex);
	i=lookup_extent(path, extent);
	pthread_rwlock_wrlock(&dmex);
	if(i<0)
		i=extent_alloc(last, extent);
	uint32_t transferred=0, len=1<<(7+d_bsh);
	fprintf(stderr, "extent %u\n", extent);
	for(uint32_t b=blocknum;b<=endblocknum;b++)
	{
		uint16_t extent=b/(d_manyblocks?8:16);
		if(b%(d_manyblocks?8:16))
		{
			if(i>=0)
			{
				if(!d_list[i].al[b%(d_manyblocks?8:16)]) d_list[i].al[b%(d_manyblocks?8:16)]=disk_alloc();
				if(d_list[i].al[b%(d_manyblocks?8:16)])
					where=(((off_t)d_list[i].al[b%(d_manyblocks?8:16)])<<(7+d_bsh));
				else
					where=0;
			}
		}
		else if(b)
		{
			plus3_dirent last=d_list[i];
			pthread_rwlock_unlock(&dmex);
			i=lookup_extent(path, extent);
			pthread_rwlock_wrlock(&dmex);
			if(i<0)
				i=extent_alloc(last, extent);
			if(i>=0)
			{
				if(!d_list[i].al[0]) d_list[i].al[0]=disk_alloc();
				if(d_list[i].al[0])
					where=(((off_t)d_list[i].al[0])<<(7+d_bsh));
				else
					where=0;
			}
		}
		else if(noblocks)
		{
			if(i>=0)
			{
				if(!d_list[i].al[0]) d_list[i].al[0]=disk_alloc();
				if(d_list[i].al[0])
					where=(((off_t)d_list[i].al[0])<<(7+d_bsh));
				else
					where=0;
			}
		}
		if(transferred+len>size)
			len=size-transferred;
		if(i>=0)
		{
			d_list[i].rcount=(1+(b%(d_manyblocks?8:16)))<<d_bsh;
			d_list[i].bcount=0;
			d_encode(dm+i*0x20, d_list[i]);
		}
		fprintf(stderr, "b=%u, i=%d, where=%zu, transferred=%zu, len=%zu\n", b, i, (size_t)where, transferred, len);
		if((i>=0)&&where)
			memcpy(dm+where+((offset+transferred)%(1<<(7+d_bsh))), buf+transferred, len);
		transferred+=len;
	}
	size=transferred;
	pthread_rwlock_unlock(&dmex);
	return(size);
}

static int plus3_truncate(const char *path, off_t offset)
{
	if(strcmp(path, "/")==0)
	{
		return(-EISDIR);
	}
	if(path[0]!='/') return(-ENOENT);
	int32_t i=lookup(path);
	if((i<0)||(i>=(int32_t)d_ndirent))
		return(-ENOENT);
	pthread_rwlock_wrlock(&dmex);
	// grovel for the header
	off_t where=(((off_t)d_list[i].al[0])<<(7+d_bsh));
	if(memcmp(dm+where, "PLUS3DOS\032", 9)==0)
	{
		uint32_t size=read32(dm+where+11);
		uint8_t ck=0; // header checksum
		for(size_t i=0;i<127;i++)
			ck+=dm[where+i];
		if(ck==(uint8_t)dm[where+127])
		{
			offset+=128;
			if(offset<size)
			{
				write32(dm+where+11, offset);
				write16(dm+where+16, offset-128);
			}
			ck=0;
			for(size_t i=0;i<127;i++)
				ck+=dm[where+i];
			dm[where+127]=ck;
		}
	}
	else
		fprintf(stderr, "NOHEADER\n");
	// prepare path components
	path++;
	char nm[9], ex[4];
	size_t ne,nl,ee=0;
	for(ne=0;ne<8;ne++)
	{
		if(path[ne]=='.') break;
		if(!path[ne]) break;
		nm[ne]=path[ne];
	}
	nl=ne;
	for(;ne<8;ne++)
		nm[ne]=' ';
	nm[8]=0;
	if(path[nl])
	{
		if(path[nl++]!='.') return(-1);
		for(;ee<3;ee++)
		{
			if(!path[nl+ee]) break;
			ex[ee]=path[nl+ee];
		}
	}
	for(;ee<3;ee++)
		ex[ee]=' ';
	ex[3]=0;
	if(!offset)
	{
		d_list[i].rcount=d_list[i].bcount=0;
		for(unsigned int b=0;b<(d_manyblocks?8:16);b++)
		{
			if(d_list[i].al[b])
				d_bitmap[d_list[i].al[b]]=false;
			d_list[i].al[b]=0;
		}
		d_encode(dm+i*0x20, d_list[i]);
		for(uint32_t i=0;i<d_ndirent;i++)
		{
			if((d_list[i].status<16)&&(d_list[i].xnum))
			{
				if(!memcmp(nm, d_list[i].name, 8))
					if(!memcmp(ex, d_list[i].ext, 3))
					{
						for(unsigned int b=0;b<(d_manyblocks?8:16);b++)
						{
							if(d_list[i].al[b])
								d_bitmap[d_list[i].al[b]]=false;
							d_list[i].al[b]=0;
						}
						d_list[i].status=0xe5;
						d_encode(dm+i*0x20, d_list[i]);
					}
			}
		}
		pthread_rwlock_unlock(&dmex);
		return(0);
	}
	uint32_t blocknum=(offset-1)>>(7+d_bsh);
	for(uint32_t b=0;b<=blocknum;b++)
	{
		if(i>=0)
		{
			d_list[i].rcount=(1+(b%(d_manyblocks?8:16)))<<d_bsh;
			d_list[i].bcount=0;
		}
		if(b%(d_manyblocks?8:16))
		{
			// nothing
		}
		else if(b)
		{
			uint16_t extent=b/(d_manyblocks?8:16);
			i=lookup_extent(path, extent);
		}
	}
	uint16_t extent=blocknum/(d_manyblocks?8:16);
	fprintf(stderr, "extent %u\n", extent);
	if(!((blocknum+1)%(d_manyblocks?8:16)))
	{
		if(i>=0)
		{
			d_list[i].rcount=1+((offset-1)>>7)%(1<<d_bsh);
			d_list[i].bcount=0;
			for(unsigned int b=(blocknum+1)%(d_manyblocks?8:16);b<(d_manyblocks?8:16);b++)
			{
				if(d_list[i].al[b])
					d_bitmap[d_list[i].al[b]]=false;
				d_list[i].al[b]=0;
			}
			d_encode(dm+i*0x20, d_list[i]);
		}
	}
	for(uint32_t i=0;i<d_ndirent;i++)
	{
		if((d_list[i].status<16)&&(d_list[i].xnum>extent))
		{
			if(!memcmp(nm, d_list[i].name, 8))
				if(!memcmp(ex, d_list[i].ext, 3))
				{
					for(unsigned int b=0;b<(d_manyblocks?8:16);b++)
					{
						if(d_list[i].al[b])
							d_bitmap[d_list[i].al[b]]=false;
						d_list[i].al[b]=0;
					}
					d_list[i].status=0xe5;
					d_encode(dm+i*0x20, d_list[i]);
				}
		}
	}
	
	pthread_rwlock_unlock(&dmex);
	return(0);
}

static int plus3_getxattr(const char *path, const char *name, char *value, size_t vlen)
{
	if(path[0]!='/') return(-ENOENT);
	if(!path[1]) return(-ENOATTR);
	int32_t i=lookup(path);
	if((i<0)||(i>=(int32_t)d_ndirent))
		return(-ENOENT);
	pthread_rwlock_rdlock(&dmex);
	// grovel for the header
	off_t where=(((off_t)d_list[i].al[0])<<(7+d_bsh));
	bool header=false;
	size_t len=128*d_list[i].rcount+d_list[i].bcount;
	if(memcmp(dm+where, "PLUS3DOS\032", 9)==0)
	{
		uint32_t size=read32(dm+where+11);
		uint8_t ck=0; // header checksum
		for(size_t i=0;i<127;i++)
			ck+=dm[where+i];
		if(ck==(uint8_t)dm[where+127])
		{
			header=true;
			len=size;
		}
	}
	int rlen=0;
	char result[256];
	if(header&&(strcmp(name, "user.plus3dos.plus3basic.filetype")==0))
		snprintf(result, 256, "%u%n", (uint8_t)dm[where+15], &rlen);
	else if(header&&(dm[where+15]==0)&&(strcmp(name, "user.plus3dos.plus3basic.line")==0))
		snprintf(result, 256, "%u%n", (uint16_t)read16(dm+where+18), &rlen);
	else if(header&&(dm[where+15]==0)&&(strcmp(name, "user.plus3dos.plus3basic.prog")==0))
		snprintf(result, 256, "%u%n", (uint16_t)read16(dm+where+20), &rlen); /* start of the variable area relative to the start of the program */
	else if(header&&((dm[where+15]==1)||(dm[where+15]==2))&&(strcmp(name, "user.plus3dos.plus3basic.name")==0))
	{
		result[0]=dm[where+19];
		rlen=1;
	}
	else if(header&&(dm[where+15]==3)&&(strcmp(name, "user.plus3dos.plus3basic.addr")==0))
		snprintf(result, 256, "%u%n", (uint16_t)read16(dm+where+18), &rlen);
	pthread_rwlock_unlock(&dmex);
	if(!rlen) return(-ENOATTR);
	if(vlen)
	{
		if((int)vlen<rlen)
			return(-ERANGE);
		memcpy(value, result, rlen);
	}
	return(rlen);
}

static int plus3_setxattr(const char *path, const char *name, const char *value, size_t vlen, int flags)
{
	if(path[0]!='/') return(-ENOENT);
	if(!path[1]) return(-ENOATTR);
	int32_t i=lookup(path);
	if((i<0)||(i>=(int32_t)d_ndirent))
		return(-ENOENT);
	pthread_rwlock_rdlock(&dmex);
	// grovel for the header
	off_t where=(((off_t)d_list[i].al[0])<<(7+d_bsh));
	bool header=false;
	size_t len=128*d_list[i].rcount+d_list[i].bcount;
	if(memcmp(dm+where, "PLUS3DOS\032", 9)==0)
	{
		uint32_t size=read32(dm+where+11);
		uint8_t ck=0; // header checksum
		for(size_t i=0;i<127;i++)
			ck+=dm[where+i];
		if(ck==(uint8_t)dm[where+127])
		{
			header=true;
			len=size;
		}
	}
	pthread_rwlock_unlock(&dmex);
	char ntval[vlen+1];
	memcpy(ntval, value, vlen);
	ntval[vlen]=0;
	if(header&&(strcmp(name, "user.plus3dos.plus3basic.filetype")==0))
	{
		unsigned int ft;
		if(sscanf(value, "%u", &ft)==1)
		{
			pthread_rwlock_wrlock(&dmex);
			dm[where+15]=ft;
			uint8_t ck=0; // header checksum
			for(size_t i=0;i<127;i++)
				ck+=dm[where+i];
			dm[where+127]=ck;
			pthread_rwlock_unlock(&dmex);
			return(0);
		}
		return(-EINVAL);
	}
	else if(header&&(dm[where+15]==0)&&(strcmp(name, "user.plus3dos.plus3basic.line")==0))
	{
		unsigned int ln;
		if(sscanf(value, "%u", &ln)==1)
		{
			pthread_rwlock_wrlock(&dmex);
			dm[where+18]=ln;
			dm[where+19]=ln>>8;
			uint8_t ck=0; // header checksum
			for(size_t i=0;i<127;i++)
				ck+=dm[where+i];
			dm[where+127]=ck;
			pthread_rwlock_unlock(&dmex);
			return(0);
		}
		return(-EINVAL);
	}
	else if(header&&(dm[where+15]==0)&&(strcmp(name, "user.plus3dos.plus3basic.prog")==0)) /* start of the variable area relative to the start of the program */
	{
		unsigned int pr;
		if(sscanf(value, "%u", &pr)==1)
		{
			pthread_rwlock_wrlock(&dmex);
			dm[where+20]=pr;
			dm[where+21]=pr>>8;
			uint8_t ck=0; // header checksum
			for(size_t i=0;i<127;i++)
				ck+=dm[where+i];
			dm[where+127]=ck;
			pthread_rwlock_unlock(&dmex);
			return(0);
		}
		return(-EINVAL);
	}
	else if(header&&((dm[where+15]==1)||(dm[where+15]==2))&&(strcmp(name, "user.plus3dos.plus3basic.name")==0))
	{
		if(value[0])
		{
			pthread_rwlock_wrlock(&dmex);
			dm[where+19]=value[0];
			uint8_t ck=0; // header checksum
			for(size_t i=0;i<127;i++)
				ck+=dm[where+i];
			dm[where+127]=ck;
			pthread_rwlock_unlock(&dmex);
			return(0);
		}
		return(-EINVAL);
	}
	else if(header&&(dm[where+15]==3)&&(strcmp(name, "user.plus3dos.plus3basic.addr")==0))
	{
		unsigned int ad;
		if(sscanf(value, "%u", &ad)==1)
		{
			pthread_rwlock_wrlock(&dmex);
			dm[where+18]=ad;
			dm[where+19]=ad>>8;
			uint8_t ck=0; // header checksum
			for(size_t i=0;i<127;i++)
				ck+=dm[where+i];
			dm[where+127]=ck;
			pthread_rwlock_unlock(&dmex);
			return(0);
		}
		return(-EINVAL);
	}
	return(-ENOATTR);
}

static int plus3_listxattr(const char *path, char *list, size_t size)
{
	if(path[0]!='/') return(-ENOENT);
	if(!path[1]) return(0);
	int32_t i=lookup(path);
	if((i<0)||(i>=(int32_t)d_ndirent))
		return(-ENOENT);
	pthread_rwlock_rdlock(&dmex);
	// grovel for the header
	off_t where=(((off_t)d_list[i].al[0])<<(7+d_bsh));
	bool header=false;
	size_t len=128*d_list[i].rcount+d_list[i].bcount;
	if(memcmp(dm+where, "PLUS3DOS\032", 9)==0)
	{
		uint32_t size=read32(dm+where+11);
		uint8_t ck=0; // header checksum
		for(size_t i=0;i<127;i++)
			ck+=dm[where+i];
		if(ck==(uint8_t)dm[where+127])
		{
			header=true;
			len=size;
		}
	}
	size_t nxattrs=0;
	const char *xattrs[256];
	if(header)
	{
		xattrs[nxattrs++]="user.plus3dos.plus3basic.filetype";
		switch(dm[where+15]) // filetype
		{
			case 0:
				xattrs[nxattrs++]="user.plus3dos.plus3basic.line";
				xattrs[nxattrs++]="user.plus3dos.plus3basic.prog";
			break;
			case 1:
			case 2:
				xattrs[nxattrs++]="user.plus3dos.plus3basic.name";
			break;
			case 3:
				xattrs[nxattrs++]="user.plus3dos.plus3basic.addr";
			break;
		}
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

static struct fuse_operations plus3_oper = {
	.getattr	= plus3_getattr,
	/*.access		= plus3_access,
	.readlink	= plus3_readlink,*/
	.readdir	= plus3_readdir,
	/*.mknod		= plus3_mknod,
	.mkdir		= plus3_mkdir,
	.symlink	= plus3_symlink,*/
	.unlink		= plus3_unlink,
	/*.rmdir		= plus3_rmdir,
	.rename		= plus3_rename,
	.link		= plus3_link,
	.chmod		= plus3_chmod,
	.chown		= plus3_chown,*/
	.truncate	= plus3_truncate,
	/*.utimens	= plus3_utimens,*/
	.open		= plus3_open,
	.create		= plus3_create,
	.read		= plus3_read,
	.write		= plus3_write,
	/*.statfs		= plus3_statfs,
	.release	= plus3_release,
	.fsync		= plus3_fsync,*/
	.setxattr	= plus3_setxattr,
	.getxattr	= plus3_getxattr,
	.listxattr	= plus3_listxattr,
	/*.removexattr= plus3_removexattr,*/
};

int main(int argc, char *argv[])
{
	if(argc<3)
	{
		fprintf(stderr, "Usage: plus3dosfs <part-image> <mountpoint> [options]\n");
		return(1);
	}
	if(pthread_rwlock_init(&dmex, NULL))
	{
		perror("plus3dosfs: pthread_rwlock_init");
		return(1);
	}
	const char *df=argv[1];
	struct stat st;
	if(stat(df, &st))
	{
		fprintf(stderr, "plus3dosfs: Failed to stat '%s'\n", df);
		perror("\tstat");
		pthread_rwlock_destroy(&dmex);
		return(1);
	}
	char ptbuf[4];
	ssize_t ptlen;
	if((ptlen=getxattr(df, "user.idedos.pt", ptbuf, sizeof ptbuf))<0)
	{
		perror("plus3dosfs: getxattr");
		return(1);
	}
	if(strncmp(ptbuf, "3", ptlen))
	{
		fprintf(stderr, "plus3dosfs: '%s' is not a +3DOS partition\n\tuser.idedos.pt=%s\n", df, ptbuf);
		return(1);
	}
	d_sz=st.st_size;
	fprintf(stderr, "plus3dosfs: '%s' size is %jdB", df, (intmax_t)d_sz);
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
	int dfd=open(df, O_RDWR);
	if(dfd<0)
	{
		perror("plus3dosfs: open");
		pthread_rwlock_destroy(&dmex);
		return(1);
	}
	if(flock(dfd, LOCK_EX|LOCK_NB))
	{
		if(errno==EWOULDBLOCK)
		{
			fprintf(stderr, "plus3dosfs: '%s' is locked by another process (flock: EWOULDBLOCK)\n", df);
		}
		else
			perror("plus3dosfs: flock");
		pthread_rwlock_destroy(&dmex);
		return(1);
	}
	dm=mmap(NULL, d_sz, PROT_READ|PROT_WRITE, MAP_SHARED|MAP_POPULATE, dfd, 0);
	if(!dm)
	{
		perror("plus3dosfs: mmap");
		flock(dfd, LOCK_UN);
		close(dfd);
		pthread_rwlock_destroy(&dmex);
		return(1);
	}
	fprintf(stderr, "plus3dosfs: '%s' mmap()ed in\n", df);
	int rv=EXIT_FAILURE;
	
	char ndbuf[6];
	ssize_t ndlen;
	if((ndlen=getxattr(df, "user.plus3dos.xdpb.ndirent", ndbuf, sizeof ndbuf))<0)
	{
		perror("plus3dosfs: getxattr");
		goto shutdown;
	}
	ndbuf[ndlen]=0;
	if(sscanf(ndbuf, "%u", &d_ndirent)!=1)
	{
		fprintf(stderr, "plus3dosfs: Bad user.plus3dos.xdpb.ndirent = %s\n", ndbuf);
		goto shutdown;
	}
	if(!(d_list=malloc(d_ndirent*sizeof(plus3_dirent))))
	{
		perror("plus3dosfs: malloc");
		goto shutdown;
	}
	if((ndlen=getxattr(df, "user.plus3dos.xdpb.nblocks", ndbuf, sizeof ndbuf))<0)
	{
		perror("plus3dosfs: getxattr");
		goto shutdown;
	}
	ndbuf[ndlen]=0;
	if(sscanf(ndbuf, "%u", &d_nblocks)!=1)
	{
		fprintf(stderr, "plus3dosfs: Bad user.plus3dos.xdpb.nblocks = %s\n", ndbuf);
		goto shutdown;
	}
	d_manyblocks=(d_nblocks>255);
	if(!(d_bitmap=malloc(d_nblocks*sizeof(bool))))
	{
		perror("plus3dosfs: malloc");
		goto shutdown;
	}
	memset(d_bitmap, 0, d_nblocks*sizeof(bool)); // set them all to false (free)
	char bshbuf[6];
	ssize_t bshlen;
	if((bshlen=getxattr(df, "user.plus3dos.xdpb.bsh", bshbuf, sizeof bshbuf))<0)
	{
		perror("plus3dosfs: getxattr");
		goto shutdown;
	}
	bshbuf[bshlen]=0;
	if(sscanf(bshbuf, "%hhu", &d_bsh)!=1)
	{
		fprintf(stderr, "plus3dosfs: Bad user.plus3dos.xdpb.bsh = %s\n", bshbuf);
		goto shutdown;
	}
	for(size_t i=0;(i<<(7+d_bsh))<0x20*d_ndirent;i++) // mark the dirents' blocks as used
		d_bitmap[i]=true;
	
	size_t uents=0;
	for(size_t i=0;i<d_ndirent;i++)
	{
		char dbuf[0x20];
		dread(dbuf, 0x20, i*0x20);
		d_list[i]=d_decode(dbuf);
		if(d_list[i].status!=0xe5)
			uents++;
		if(d_list[i].status<16)
		{
			fprintf(stderr, "%.8s.%.3s %04x\n", d_list[i].name, d_list[i].ext, (unsigned int)d_list[i].xnum);
			for(unsigned int b=0;b<(d_manyblocks?8:16);b++)
				if(d_list[i].al[b]) d_bitmap[d_list[i].al[b]]=true;
		}
	}
	fprintf(stderr, "plus3dosfs: Used %zu of %zu dirents\n", uents, d_ndirent);
	
	int fargc=argc-1;
	char **fargv=(char **)malloc(fargc*sizeof(char *));
	fargv[0]=argv[0];
	for(int i=1;i<fargc;i++)
		fargv[i]=argv[i+1];
	
	rv=fuse_main(fargc, fargv, &plus3_oper, NULL);
	shutdown:
	pthread_rwlock_wrlock(&dmex);
	munmap(dm, d_sz);
	flock(dfd, LOCK_UN);
	close(dfd);
	pthread_rwlock_unlock(&dmex);
	pthread_rwlock_destroy(&dmex);
	return(rv);
}

void dread(char *buf, size_t bytes, off_t offset)
{
	if(!buf) return;
	pthread_rwlock_rdlock(&dmex);
	memcpy(buf, dm+offset, bytes);
	pthread_rwlock_unlock(&dmex);
}

/*
	St F0 F1 F2 F3 F4 F5 F6 F7 E0 E1 E2 Xl Bc Xh Rc
	Al Al Al Al Al Al Al Al Al Al Al Al Al Al Al Al
	uint8_t status;
	char name[8];
	char ext[3];
	bool ro,sys,ar;
	uint16_t xnum; // extent number
	uint8_t rcount; // count of records in last used logical extent
	uint8_t bcount; // count of bytes in last used record
	uint16_t al[16]; // block pointers
*/
static plus3_dirent d_decode(const char buf[0x20])
{
	plus3_dirent rv;
	rv.status=buf[0];
	for(size_t i=0;i<8;i++)
		rv.name[i]=buf[i+1]&0x7f;
	for(size_t i=0;i<3;i++)
		rv.ext[i]=buf[i+9]&0x7f;
	rv.ro=buf[9]&0x80;
	rv.sys=buf[10]&0x80;
	rv.ar=buf[11]&0x80;
	rv.xnum=(buf[12]&0x1f)|((buf[14]&0x3f)<<5);
	rv.bcount=buf[13];
	rv.rcount=buf[15];
	if(d_manyblocks)
		for(size_t i=0;i<8;i++)
			rv.al[i]=read16(buf+0x10+(i<<1));
	else
		memcpy(rv.al, buf+0x10, 0x10);
	return(rv);
}

static void d_encode(char buf[0x20], plus3_dirent src)
{
	buf[0]=src.status;
	for(size_t i=0;i<8;i++)
		buf[i+1]=src.name[i]&0x7f;
	for(size_t i=0;i<3;i++)
		buf[i+9]=src.ext[i]&0x7f;
	if(src.ro) buf[9]|=0x80;
	if(src.sys) buf[10]|=0x80;
	if(src.ar) buf[11]|=0x80;
	buf[12]=src.xnum&0x1f;
	buf[14]=(src.xnum>>5)&0x3f;
	buf[13]=src.bcount;
	buf[15]=src.rcount;
	if(d_manyblocks)
		for(size_t i=0;i<8;i++)
		{
			buf[0x10+(i<<1)]=src.al[i]&0xff;
			buf[0x11+(i<<1)]=(src.al[i]>>8)&0xff;
		}
	else
		memcpy(buf+0x10, src.al, 0x10);
}

static int32_t lookup(const char *path)
{
	return(lookup_extent(path, 0));
}

static int32_t lookup_extent(const char *path, uint16_t extent)
{
	if(*path++!='/') return(-1);
	char nm[9], ex[4];
	size_t ne,nl,ee=0;
	for(ne=0;ne<8;ne++)
	{
		if(path[ne]=='.') break;
		if(!path[ne]) break;
		nm[ne]=path[ne];
	}
	nl=ne;
	for(;ne<8;ne++)
		nm[ne]=' ';
	nm[8]=0;
	if(path[nl])
	{
		if(path[nl++]!='.') return(-1);
		for(;ee<3;ee++)
		{
			if(!path[nl+ee]) break;
			ex[ee]=path[nl+ee];
		}
	}
	for(;ee<3;ee++)
		ex[ee]=' ';
	ex[3]=0;
	pthread_rwlock_rdlock(&dmex);
	for(uint32_t i=0;i<d_ndirent;i++)
	{
		if((d_list[i].status<16)&&(d_list[i].xnum==extent))
		{
			if(!memcmp(nm, d_list[i].name, 8))
				if(!memcmp(ex, d_list[i].ext, 3))
				{
					pthread_rwlock_unlock(&dmex);
					return(i);
				}
		}
	}
	pthread_rwlock_unlock(&dmex);
	return(-1);
}

uint16_t disk_alloc(void)
{
	for(uint32_t i=1;i<d_nblocks;i++)
	{
		if(!d_bitmap[i])
		{
			d_bitmap[i]=true;
			fprintf(stderr, "disk_alloc: %zu\n", i);
			return(i);
		}
	}
	return(0);
}

static int32_t extent_alloc(plus3_dirent last, uint16_t extent)
{
	for(uint32_t i=0;i<d_ndirent;i++)
	{
		if(d_list[i].status==0xe5)
		{
			d_list[i]=last;
			d_list[i].xnum=extent;
			d_list[i].rcount=d_list[i].bcount=0;
			memset(d_list[i].al, 0, 0x10);
			d_encode(dm+i*0x20, d_list[i]);
			fprintf(stderr, "extent_alloc: %zu\n", i);
			return(i);
		}
	}
	return(-1);
}
