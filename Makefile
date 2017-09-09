
libcoll-jpeg.so: md5.c md5coll.c md5.h
	gcc -shared -fpic -o libcoll-jpeg.so -Wall  -O3  -DNDEBUG=1 -DJPEGHACK=1 md5.c md5coll.c

