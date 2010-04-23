CFLAGS = -g `epic -includedirs`

go: bittwiddle.o
	idris IPDSL.idr

bittwiddle.o: bittwiddle.h bittwiddle.c

twiddletest: bittwiddle.o twiddletest.idr
	idris twiddletest.idr
#	gcc bittwiddle.o `epic -libdirs` -levm -lgc -o twiddletest

recvtest: bittwiddle.o bittwiddle.idr recvtest.idr packetformat.idr
	idris recvtest.idr -o recvtest

sendtest: bittwiddle.o bittwiddle.idr sendtest.idr packetformat.idr
	idris sendtest.idr -o sendtest
