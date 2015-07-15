DESTDIR=

DEMOS= dwyerdt guibasdt mst

CFLAGS = -O


common: common.c
	cc common.c -o common -lm ${WINLIBS}
	strip common
	rm -f guibasdt dwyerdt vd mst
	ln common guibasdt
	ln common dwyerdt
	ln common vd
	ln common mst

clean:
	rm -f *.o errs core ${DEMOS}
