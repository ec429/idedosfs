# ffs Makefile

CC := gcc
CFLAGS := -Wall -Wextra -Werror -Wno-unused -pedantic --std=gnu99 -g
FUSEFLAGS := `pkg-config fuse --cflags`
FUSELIBS := `pkg-config fuse --libs`

all: idedosfs plus3dosfs

idedosfs: idedosfs.c
	$(CC) $(CFLAGS) $(FUSEFLAGS) $(CPPFLAGS) $(LDFLAGS) -o $@ $< $(LIBS) $(FUSELIBS)

plus3dosfs: plus3dosfs.c
	$(CC) $(CFLAGS) $(FUSEFLAGS) $(CPPFLAGS) $(LDFLAGS) -o $@ $< $(LIBS) $(FUSELIBS)

clean:
	rm plus3dosfs

