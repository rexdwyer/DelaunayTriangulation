#define POSTSCRIPT
/****************************************************************/
/*	DELAUNAY TRIANGULATION 
/*	VORONOI DIAGRAM 
/*	MINIMUM SPANNING TREE 
/*
/*		Rex A. Dwyer
/*
/*	This program implements the Delaunay triangulation and Voronoi 
/*	diagram algorithms of:
/*
/*	L.J. Guibas & J. Stolfi, "Primitives for the manipulation of 
/*	general subdivisions and the computation of Voronoi diagrams",
/*	ACM Transactions on Graphics 4 (1985), 74-123.
/*
/*	and
/*
/*	R.A. Dwyer, "A simple divide-and-conquer algorithm for 
/*	constructing Delaunay triangulations in O(n log log n) expected
/*	time", 2nd Symposium on Computational Geometry (1986), 276-284.
/*
/*	The algorithm for traversing and outputting the computed graph
/*	without using additional storage is that of:
/*
/*	H. Edelsbrunner, L.J. Guibas & J. Stolfi, "Optimal Point Location
/*	in a Monotone Subdivision", DEC SRC Report #2 (1984), 22-27.
/*
/*	The round-robin minimum-spanning-tree algorithm is described
/*	in:
/*
/*	R.E.Tarjan, Data Structures and Network Algorithms, SIAM, 1983.
/****************************************************************/

#include <stdio.h>
#include <math.h>
#define TRUE 1
#define FALSE 0

#define EPSILON (1.0e-6)
#define drand() (((double) rand()) / (double) 0x7fffffff)

/* Clearly wrong, but good enough for now: */
#define MAXDOUBLE 1.0e10
#define MINDOUBLE (-1.0e10)

#define BOOLEAN int

typedef int EDGE_PTR;

typedef unsigned short VERTEX_PTR;

struct VEC2 {
double x,y;
};

struct VERTEX {
    struct VEC2 v;
    union {
	double norm;
	struct {
	    VERTEX_PTR father;
	    short count;
	    EDGE_PTR heap;
	    } vstruct;
	} vunion;
};

#define onext(a) next[a]
#define oprev(a) rot(onext(rot(a)))
#define lnext(a) rot(onext(rotinv(a)))
#define lprev(a) sym(onext(a))
#define rnext(a) rotinv(onext(rot(a)))
#define rprev(a) onext(sym(a))
#define dnext(a) sym(onext(sym(a)))
#define dprev(a) rotinv(onext(rotinv(a)))

#define X(a) va[a].v.x
#define Y(a) va[a].v.y
#define NORM(a) va[a].vunion.norm
#define COUNT(a) va[a].vunion.vstruct.count
#define FATHER(a) va[a].vunion.vstruct.father
#define HEAP(a) va[a].vunion.vstruct.heap
#define COLOR(e) (color[e>>2])
#define orig(a) org[a]
#define dest(a) orig(sym(a))

#define sym(a) ((a) ^ 2)
EDGE_PTR rot();
EDGE_PTR rotinv();
delete_all_edges(); 
EDGE_PTR alloc_edge();
EDGE_PTR makeedge();
splice();
swapedge();
EDGE_PTR connect();
deleteedge();
build_delaunay_triangulation();
BOOLEAN leftof();

VERTEX_PTR *vp;		/* points to array holding indices of input points */
struct VERTEX *va;	/* points to array holding domain coordinates of
   input points.  The domain coordinates of the kth
   input point are X(k-1) and Y(k-1) 
   (same as va[k-1].v.x and  va[k-1].v.y)  */
EDGE_PTR *next;		/* points to array holding "onext" pointers of edges */
VERTEX_PTR *org;	/* points to array holding "orig" pointers of edges */
double *len; 		/* points to an array holding the length of edges */
int *color; 		/* points to an array holding the color of edges */
EDGE_PTR *hq;		/* heap queue for MST */
int num_vertices;	/* the number of input points */
int speed;
BOOLEAN plot_dt_construction;
BOOLEAN plot_colorful_dt;

#define GETCOLOR(e) ((COLOR(e)<MAXCOLOR)?(COLOR(e)+1):MAXCOLOR)



/****************************************************************/
/*	Quad-edge access.  See Guibas & Stolfi.
/****************************************************************/
EDGE_PTR rot(a)
EDGE_PTR a;
{
    return( ((a + 1) & 3) | (a & ~3) );
}

EDGE_PTR rotinv(a)
EDGE_PTR a;
{
    return( ((a + 3) & 3) | (a & ~3) );
}

/****************************************************************/
/*	Quad-edge storage allocation
/****************************************************************/
EDGE_PTR next_edge, avail_edge;
#define NYL -1

delete_all_edges() { next_edge = 0; avail_edge = NYL;}

EDGE_PTR alloc_edge()
{
    EDGE_PTR ans;

    if (avail_edge == NYL) {
	ans = next_edge;
	next_edge += 4;
	}
    else {
	ans = avail_edge;
	avail_edge = onext(avail_edge);
	}
    return(ans);
}

free_edge(e)
EDGE_PTR e;
{
    e ^= e & 3;
    onext(e) = avail_edge;
    avail_edge = e;
}


/****************************************************************/
/*	Quad-edge manipulation primitives.  See Guibas & Stolfi.
/****************************************************************/
int max_hue;
EDGE_PTR makeedge(origin, destination, hue)
VERTEX_PTR origin, destination;
int hue;
{
    register EDGE_PTR temp, ans;
    temp = alloc_edge();
    ans = temp;

    onext(temp) = ans;
    orig(temp) = origin;
    onext(++temp) = ans + 3;
    onext(++temp) = ans + 2;
    orig(temp) = destination;
    onext(++temp) = ans + 1;
    COLOR(ans) = hue;
    return(ans);
};

splice(a,b)
EDGE_PTR a, b;
{
    EDGE_PTR alpha, beta, temp;
    alpha = rot(onext(a));
    beta = rot(onext(b));
    temp = onext(alpha);
    onext(alpha) = onext(beta);
    onext(beta) = temp;
    temp = onext(a);
    onext(a) = onext(b);
    onext(b) = temp;
};

swapedge(e)
EDGE_PTR e;
{
    EDGE_PTR a,b,syme;
    a = oprev(e);
    syme = sym(e);
    b = oprev(syme);
    splice(e, a);
    splice(syme, b);
    splice(e, lnext(a));
    splice(syme, lnext(b));
    orig(e) = dest(a);
    dest(e) = dest(b);
};

EDGE_PTR connect_left(a, b,hue)
EDGE_PTR a,b; int hue;
{
    register EDGE_PTR ans;
    ans = makeedge(dest(a), orig(b),hue);
    splice(ans, lnext(a));
    splice(sym(ans), b);
    return(ans);
};

EDGE_PTR connect_right(a, b,hue)
EDGE_PTR a,b; int hue;
{
    register EDGE_PTR ans;
    ans = makeedge(dest(a), orig(b), hue);
    splice(ans, sym(a));
    splice(sym(ans), oprev(b));
    return(ans);
};

deleteedge(e)
/* disconnects e from the rest of the structure and destroys it. */
EDGE_PTR e;
{
    splice(e, oprev(e));
    splice(sym(e), oprev(sym(e)));
    free_edge(e);
};

/****************************************************************/
/*	Geometric primitives.  See Guibas & Stolfi.
/****************************************************************/
BOOLEAN incircle(a,b,c,d)
/* TRUE if d lies inside the circle defined by a, b, and c. */
VERTEX_PTR a,b,c,d;
{
    double adx, ady, bdx, bdy, cdx, cdy, dx, dy, dnorm;
    /*
    fprintf(stderr,"incircle parameters:\n%lf %lf\n%lf %lf\n%lf %lf/n%lf %lf\n",
    X(a),Y(a),X(b),Y(b),X(c),Y(c),X(d),Y(d));
    */
    dx = X(d);	dy = Y(d);	dnorm = NORM(d);
    adx = X(a) - dx;    ady = Y(a) - dy;    
    bdx = X(b) - dx;    bdy = Y(b) - dy;    
    cdx = X(c) - dx;    cdy = Y(c) - dy;    
    if (0.0 <
	(  (NORM(a) - dnorm) * (bdx * cdy - bdy * cdx)
	+ (NORM(b) - dnorm) * (cdx * ady - cdy * adx)
	+ (NORM(c) - dnorm) * (adx * bdy - ady * bdx))) {
	return(TRUE);
    }
    else {
	return(FALSE);
    }
};

BOOLEAN ccw(a,b,c)
/* TRUE iff A, B, C form a counterclockwise oriented triangle */
VERTEX_PTR a,b,c;
{
    double xc, yc;
    xc = X(c); yc = Y(c);
    if ( ((X(a)-xc) * (Y(b)-yc) - (X(b)-xc) * (Y(a)-yc)) > 0.0 )
        return (TRUE);
    else
        return(FALSE);
};

BOOLEAN leftof(qx,qy,e)
double qx,qy;
EDGE_PTR e;
/* TRUE iff (qx,qy) lies to the left of the edge e */
/* similar to ccw */
{
    register VERTEX_PTR a,b;
    a = dest(e);
    b = orig(e);
    if ( ((X(a)-qx) * (Y(b)-qy) - (X(b)-qx) * (Y(a)-qy)) < 0.0 )
        return (TRUE);
    else
        return(FALSE);
};

/****************************************************************/
/*	The Merge Procedure.  See Guibas & Stolfi.
/****************************************************************/
#define valid(l) ccw(orig(basel), dest(l), dest(basel))

merge_delaunay(ldo, ldi, rdi, rdo)
EDGE_PTR ldi, rdi, *ldo, *rdo;
{
BOOLEAN rvalid, lvalid;
register EDGE_PTR basel,lcand,rcand,t;
int lhue, rhue;
while (TRUE) {
    while (ccw(orig(ldi), dest(ldi), orig(rdi))) ldi = lnext(ldi);
    if (ccw(dest(rdi), orig(rdi), orig(ldi))) rdi = rprev(rdi);
    else break;
    }

basel = connect_left(sym(rdi), ldi, 0);
lcand = rprev(basel);
rcand = oprev(basel);
if (orig(basel) == orig(*rdo)) *rdo = basel;
if (dest(basel) == orig(*ldo)) *ldo = sym(basel);
lhue = 0 ; rhue = 0;

while (TRUE) {
    if (/* valid(lcand) && */ valid(t=onext(lcand))) {
	while (incircle(dest(lcand), dest(t), orig(lcand), orig(basel))) {
	    lhue += COLOR(lcand)+1;
	    deleteedge(lcand);
	    lcand = t;
	    t = onext(lcand);
	}
    }
    if (/* valid(rcand) && */ valid(t=oprev(rcand))) {
	while (incircle(dest(t), dest(rcand), orig(rcand), dest(basel))) {
	    rhue += COLOR(rcand)+1;
	    deleteedge(rcand);
	    rcand = t;
	    t = oprev(rcand);
	}
    }

lvalid = valid(lcand);
rvalid = valid(rcand);
if ((! lvalid) && (! rvalid)) return;

if (!lvalid || (rvalid
&& incircle(dest(lcand), orig(lcand), orig(rcand), dest(rcand)))){
    basel = connect_left(rcand, sym(basel), rhue);
    rhue = 0;
    rcand = lnext(sym(basel));
    }
else {
    basel = sym(connect_right(lcand, basel, lhue));
    lhue = 0;
    lcand = rprev(basel);
    }
}
};

/****************************************************************/
/*	Recursive Delaunay Triangulation Procedure.  See Guibas & Stolfi.
/*	Contains modifications for axis-switching division.  See Dwyer.
/****************************************************************/

build_delaunay(vp, lo, hi, le, re, rows)
VERTEX_PTR vp[];
int lo,hi,rows;
EDGE_PTR *le,*re;
{
EDGE_PTR a,b,c,ldo,rdi,ldi,rdo;
int split, lowrows;
register int low, high, maxx, minx;
VERTEX_PTR s1, s2, s3;

low = lo; high = hi;

if (low < (high-2)) {
    /* more than three elements; do recursion */
    minx = vp[low]; maxx = vp[high];
    if (rows == 1) {	/* time to switch axis of division */
	vpsorty(low, high);
	rows = 65536;
	}	  
	lowrows = rows>>1;
    split = low - 1 + (int) (0.5 +
	((double)(high-low+1) * ((double)lowrows / (double)rows)));
    build_delaunay(vp, low, split, &ldo, &ldi, lowrows);
    build_delaunay(vp, split+1, high, &rdi, &rdo, (rows-lowrows));
    merge_delaunay(&ldo, ldi, rdi, &rdo);
    while (orig(ldo) != minx) ldo = rprev(ldo);
    while (orig(rdo) != maxx) rdo = lprev(rdo);
    *le = ldo;
    *re = rdo;
    }
else if (low >= (high - 1)) {	/* two or one points */
    a = makeedge(vp[low], vp[high], 0);
    *le = a;
    *re = sym(a);
    if (low==high) {fprintf(stderr,"ERROR: Only 1 point!\n"); fflush(stdout);}
    }
else { /*  (low == (high - 2))  */	/* three points */
    /* 3 cases: triangles of 2 orientations, and 3 points on a line. */
    a = makeedge((s1 = vp[low]), (s2 = vp[low+1]), 0);
    b = makeedge(s2, (s3 = vp[high]), 0);
    splice(sym(a), b);
    c = connect_left(b, a, 0);
    if (ccw(s1, s3, s2)) {
    *le = sym(c);
    *re = c;
    }
else {
    *le = a;
    *re = sym(b);
    if (!ccw(s1, s2, s3)) deleteedge(c);    /* colinear */
    }
}
};

/****************************************************************/
/*	Sorting Routines
/*	These are quite a bit faster than the system sort.
/*	We always assume the existence of vp[low-1] and vp[high+1].
/*	We tinker with these, then restore them.  See J. Bentley,
/*	Writing Efficient Code, pp. 113-121.
/****************************************************************/
vpsortx(low, high)  /* Sorts by increasing x-coordinate. */
int low, high;
{
    VERTEX_PTR *lowp, *highp;
    double savelowx, savehighx;
    lowp = &(vp[low]);           highp = &(vp[high]);
    savelowx = X(*(lowp-1));     savehighx = X(*(highp+1));
    X(*(lowp-1)) = MINDOUBLE;    X(*(highp+1)) = MAXDOUBLE;
    vpsortxh(lowp, highp);
    X(*(lowp-1)) =  savelowx;    X(*(highp+1)) = savehighx;
}

vpsortxh(lowp, highp)
VERTEX_PTR *lowp, *highp;
{
if (highp - lowp <= 5) { /* Bubble Sort */
    register VERTEX_PTR *p, *q, *q1, t;
    double maxkey, qkey;
    for (p=highp; p>lowp; p--) {
	maxkey = X(*lowp);
	for (q=lowp+1; q<=p; q++) {
	    qkey = X(*q);
	    if (maxkey > qkey) {
		q1 = q-1;
		t = *q1; *q1 = *q; *q = t;
		}
	    else maxkey = qkey;
	}
    }
}
else { /* Quicksort */
    double key;
    register VERTEX_PTR *hip, *lop, t, *midp;
    midp = lowp + (highp - lowp) / 2;
    t = *lowp; *lowp = *midp; *midp = t;
    key = X(*lowp);
    for (lop=lowp; X(*lop) < key; lop++);
    for (hip=highp; X(*hip) >= key; hip--);
    while (lop <= hip) {
	t = *lop; *lop = *hip; *hip = t;
	for (lop++; X(*lop) < key; lop++);
	for (hip--; X(*hip) >= key; hip--);
	}
    vpsortxh(lowp, lop-1);
    vpsortxh(hip+1, highp);
    }
}

vpsorty(low, high)  /* Sorts by DEcreasing y-coordinate. */
int low, high;
{
    VERTEX_PTR *lowp, *highp;
    double savelowy, savehighy;
    lowp = &(vp[low]);            highp = &(vp[high]);
    savelowy = Y(*(lowp-1));      savehighy = Y(*(highp+1));
    Y(*(lowp-1)) = MAXDOUBLE;     Y(*(highp+1)) = MINDOUBLE;
    vpsortyh(lowp, highp);
    Y(*(lowp-1)) =  savelowy;     Y(*(highp+1)) = savehighy;
}

vpsortyh(lowp, highp)
VERTEX_PTR *lowp, *highp;
{
if (highp - lowp <= 5) { /* Bubble Sort */
    register VERTEX_PTR *p, *q, *q1, t;
    double minkey, qkey;
    for (p=highp; p>lowp; p--) {
	minkey = Y(*lowp);
	for (q=lowp+1; q<=p; q++) {
	    qkey = Y(*q);
	    if (minkey < qkey) {
		q1 = q-1;
		t = *q1; *q1 = *q; *q = t;
		}
	    else minkey = qkey;
	    }
	}
    }
else { /* Quicksort */
    double key;
    register VERTEX_PTR *hip, *lop, t, *midp;
    midp = lowp + (highp - lowp) / 2;
    t = *lowp; *lowp = *midp; *midp = t;
    key = Y(*lowp);
    for (lop=lowp; Y(*lop) > key; lop++);
    for (hip=highp; Y(*hip) <= key; hip--);
    while (lop <= hip) {
	t = *lop; *lop = *hip; *hip = t;
	for (lop++; Y(*lop) > key; lop++);
	for (hip--; Y(*hip) <= key; hip--);
	}
    vpsortyh(lowp, lop-1);
    vpsortyh(hip+1, highp);
    }
}


/****************************************************************/
/*	Delaunay Triangulation Output Routines
/*	See Edelsbrunner, Guibas, & Stolfi
/****************************************************************/

/* plots a site on your favorite device. */
plot_site(v) VERTEX_PTR v; {
#ifdef POSTSCRIPT
	printf("p%d drawsite\n", v);
#endif
 }

/* plots a Delaunay-triangulation edge on your favorite device. */
plot_dt_edge(e)
   EDGE_PTR e;
{
#ifdef POSTSCRIPT
	printf("p%d p%d drawseg\n", orig(e), dest(e));
#endif
}

BOOLEAN forward(e, base)
EDGE_PTR e, base;
{
    if (e == base) return(TRUE);
    if (e == sym(base)) return(FALSE);
    return(X(orig(e)) > X(dest(e)));
}


output_colorful_delaunay_triangulation(left, right)
EDGE_PTR left, right;
{
#ifdef GRAPHICS
    EDGE_PTR base, e;
    VERTEX_PTR u;
    int curcolor;

    base = connect_left(sym(left), right, -1);
    /* delete_all_retained_segments(); */
    create_retained_segment(3);
    for (curcolor=1; curcolor<=MAXCOLOR; curcolor++) {
	u = dest(base);
	e = sym(dnext(base));
	while (TRUE) {
	    while ( (e!=base) && !forward(dnext(e),base) ) {
		u = dest(e);
		e = sym(dnext(e));
	    }
	    if ((e!=base)&&(GETCOLOR(e)==curcolor)) plot_dt_edge(e,COLOR(e));
	    while (!forward(onext(e),base)) {
		plot_site(u);
		if (u == dest(base)) goto nextcolor;
		e = sym(onext(e));
		while (forward(dnext(e),base)) e = dnext(e);
		u = orig(e);
		if (GETCOLOR(e)==curcolor) plot_dt_edge(e,COLOR(e));
	    }
	    e = onext(e);
	}
nextcolor:
	e=e;
    }
    close_retained_segment();
    deleteedge(base); 
#endif
}

output_delaunay_triangulation(left, right)
EDGE_PTR left, right;
{
    EDGE_PTR base, e;
    VERTEX_PTR u;

    base = connect_left(sym(left), right, -1);
    u = dest(base);
    e = sym(dnext(base));
    while (TRUE) {
	while ( (e!=base) && !forward(dnext(e),base) ) {
	    u = dest(e);
	    e = sym(dnext(e));
	}
	if (e != base) plot_dt_edge(e,COLOR(e));
	while (!forward(onext(e),base)) {
	    plot_site(u);
	    if (u == dest(base)) {
		deleteedge(base); 
		return;
	    }
	    e = sym(onext(e));
	    while (forward(dnext(e),base)) e = dnext(e);
	    u = orig(e);
	    plot_dt_edge(e,COLOR(e));
	    }
	e = onext(e);
    }
}



/****************************************************************/
/*	Convex (Affine) Interpolation routine.  
/*
/*	Input: three vertices of a triangle p1, p2, p3,
/*	       a fourth point q=(qx,qy).
/*
/*	Output: a, b, c such that q = a*p1 + b*p2 + c*p3.
/*	        If q lies inside the triangle, then a,b,c>=0.
/****************************************************************/

convcomb(p1,p2,p3,qx,qy,a,b,c)
VERTEX_PTR p1,p2,p3;
double qx, qy;
double *a, *b, *c;
{
    register double x1,x2,y1,y2,det,t;
    t = X(p3);
    x1 = X(p1) - t;
    x2 = X(p2) - t;
    qx -= t;
    t = Y(p3);
    y1 = Y(p1) - t;
    y2 = Y(p2) - t;
    qy -= t;

    det = (x1*y2 - x2*y1);
    *a = (qx*y2 - qy*x2) / det;
    *b = (x1*qy - y1*qx) / det;
    *c = 1.0 - *a - *b;
/*
    fprintf(stderr,"\nq: (%lf,%lf) = \n", qx+X(p3), qy+X(p3));
    fprintf(stderr,"%lf * (%lf,%lf) + ", *a, X(p1), Y(p1));
    fprintf(stderr,"%lf * (%lf,%lf) + ", *b, X(p2), Y(p2));
    fprintf(stderr,"%lf * (%lf,%lf)\n", *c, X(p3), Y(p3));
    fprintf(stderr,"   (%lf,%lf), (%lf,%lf)\n\n", x1,y1,x2,y2);
*/
}

/****************************************************************/
/*	Locating a point in the triangulation.  See Guibas & Stolfi.

/*
/*	Input: ein, any edge in the triangulation.
/*	       (x, y), the point to locate.
/*
/*	Returns: an edge e of the triangle containing (x,y) such that
/*	         (x,y) lies to the left of e
/*
/*	This routine is intended to work only for points falling
/*	inside the convex hull of the triangulation.  In case some
/*	floating-point anomaly causes it to be called with a point
/*	outside, we count the number of edges we've look at to break
/*	potential infinite loops.  There are always <3*num_vertices 
/*	edges in the triangulation.  (Euler's formula)
/****************************************************************/
EDGE_PTR locate(ein,x,y)
EDGE_PTR ein;
double x, y;
{
    double qx, qy;
    register EDGE_PTR e;
    register int cnt;
    qx=x; qy=y;
    cnt = 3*num_vertices;
    e = ein;
    if (!leftof(qx,qy,e)) e = sym(e);
    while (--cnt) {
	if (leftof(qx,qy,onext(e))) e = onext(e);
	else if (leftof(qx,qy,dprev(e))) e = dprev(e);
	else return(e);
    }
    fprintf(stderr,"locate: breaking loop\n");
    return(ein);
}


/****************************************************************/
/*	Voronoi Diagram Routines.
/*		DISCARD BELOW IF ONLY DT IS NEEDED
/****************************************************************/

#define origv(a) va[orig(a)].v
#define destv(a) va[dest(a)].v
struct VEC2 circle_center();
struct VEC2 V2_sum();
struct VEC2 V2_sub();
struct VEC2 V2_times();
double V2_cprod();
struct VEC2 V2_cross();
double V2_dot();
double V2_magn();

/****************************************************************/
/*	Voronoi Output Routines
/****************************************************************/
plot_line(v1,v2)
struct VEC2 v1, v2;
{
#ifdef POSTSCRIPT
  printf("%f %f %f %f drawline\n", v1.x, v1.y, v2.x, v2.y);
#endif
}

plot_infinite_vd_edge(e)
EDGE_PTR e;
{
    struct VEC2 cvxvec, center;
    double ln;

    cvxvec = V2_sub(destv(e), origv(e));
    center = circle_center(origv(e), destv(e), destv(onext(e)));
    ln = 1.0 +
	 V2_magn(V2_sub(center,
			V2_times(0.5, V2_sum(origv(e), destv(e)))));
    plot_line(
	center, 
	V2_sum(center, V2_times(ln/V2_magn(cvxvec),V2_cross(cvxvec))));
}

plot_vd_edge(e)
EDGE_PTR e;
{
    if (ccw(orig(e), dest(e), dest(onext(e)))
	!= ccw(orig(e), dest(e), dest(oprev(e)))) {
	plot_line(
	circle_center(origv(e),destv(e),destv(onext(e))),
	circle_center(origv(e),destv(e),destv(oprev(e))));
    }
}

struct VEC2 circle_center(a,b,c)
    /* returns the center of the circle passing through A, B & C. */
struct VEC2 a,b,c;
{
    struct VEC2 p;
/*  if (V2_magn(V2_sub(b,c)) < EPSILON) {  */
    if (V2_magn(V2_sub(b,c)) < 0) {
	/* then there is no intersection point, the bisectors coincide. */
	return(V2_times(0.5, V2_sum(a,b)));
    }
    else {
        p = V2_sum(V2_times(0.5,V2_sum(a,b)),
		   V2_times(V2_dot(V2_sub(c,b), V2_sub(c,a)) /
				(-2 * V2_cprod(V2_sub(b,a), V2_sub(c,a))),
			    V2_cross(V2_sub(b,a))));
	return(p);
    }
};

output_voronoi_diagram(left, right)
EDGE_PTR left, right;
{
    EDGE_PTR base, e;
    VERTEX_PTR u;


    /* Plot infinite VD edges. */
    e = left;
    do {
	plot_infinite_vd_edge(e);
	e = onext(sym(e));
    } while (e!=left);

    base = connect_left(sym(left), right, -1);
    u = dest(base);
    e = sym(dnext(base));
    while (TRUE) {
	while ( (e!=base) && !forward(dnext(e),base) ) {
	    u = dest(e);
	    e = sym(dnext(e));
	}
	if (e != base) plot_vd_edge(e,COLOR(e));
	while (!forward(onext(e),base)) {
	    plot_site(u);
	    if (u == dest(base)) {
		deleteedge(base); 
		return;
	    }
	    e = sym(onext(e));
	    while (forward(dnext(e),base)) e = dnext(e);
	    u = orig(e);
	    plot_vd_edge(e,COLOR(e));
	    }
	e = onext(e);
    }
}


/****************************************************************/
/*	Vector Routines.
/*	From CMU vision library.  
/*	They are used only for the VD, not the DT.
/* 	They are slow because of large call-by-value parameters.
/****************************************************************/

/* V2_cprod: forms triple scalar product of [u,v,k], where k = u cross v */
/* (returns the magnitude of u cross v in space)*/

double V2_cprod(u,v)
 struct VEC2 u,v;
{
    return(u.x * v.y - u.y * v.x);
};


/* V2_dot: vector dot product */

double V2_dot(u,v)
struct VEC2 u,v;
{
    return(u.x * v.x + u.y * v.y);
};

/* V2_times: multiply a vector by a scalar */

struct VEC2 V2_times(c,v)
 double c;
 struct VEC2 v;
{
    struct VEC2 ans;
    ans.x = c * v.x;
    ans.y = c * v.y;
    return(ans);
}

/* V2_sum, V2_sub: Vector addition and subtraction */

struct VEC2 V2_sum(u,v)
 struct VEC2 u,v;
{
    struct VEC2 ans;
    
    ans.x = u.x + v.x;
    ans.y = u.y + v.y;
    return(ans);
};

struct VEC2 V2_sub(u,v)
 struct VEC2 u,v;
{
    struct VEC2 ans;
    ans.x = u.x - v.x;
    ans.y = u.y - v.y;
    return(ans);
};

/* V2_magn: magnitude of vector */

double V2_magn(u)
 struct VEC2 u;
{
    return(sqrt(u.x*u.x+u.y*u.y));
};

/* returns k X v (cross product).  this is a vector perpendicular to v */

struct VEC2 V2_cross(v)
 struct VEC2 v;
{
    struct VEC2 ans;
    ans.x = v.y;
    ans.y = -v.x;
    return(ans);
};


#define debug(S,H1,H2) { }
/*
#define debug(S,H1,H2) { \
	fprintf(stderr,S); \
	fprintf(stderr,"(");dumpedge(H1);dumpedge(H2); \
	fprintf(stderr,")\n"); fflush(stderr); \
	}
*/
#define LENGTH(e) (len[e>>2])
#define RANK(e) orig((e)+1)
#define LSON(e) onext((e))
#define RSON(e) onext((e)+1)

/****************************************************************/
/*	Find 	for Union/Find algorithm.
/****************************************************************/

VERTEX_PTR find(vv)
VERTEX_PTR vv;
{
    register int /* VERTEX_PTR */ v, vset, t;
    t = v = vv;
    vset = FATHER(t);
    while (vset != t) {
	t = vset;
	vset = FATHER(vset);
	}
    while (v != vset) {
	t = FATHER(v);
	FATHER(v) = vset;
	v = t;
	}
    return(vset);
}

/****************************************************************/
/*	Heapification.
/*	Melds the heaps stacked in the heapification queue hq.
/****************************************************************/
int hq_last;

#define init_hq()    hq_last = -1
#define insert_hq(e)    hq[++hq_last] = (e)

EDGE_PTR heapify_hq()
{
register int i;
/* fprintf(stderr,"heapify()%d\n", hq_last); fflush(stderr); */
if (hq_last == -1) return(NYL); /* empty queue */
while (hq_last > 0) {
    i = 0;
    while (i < hq_last) {
	hq[i] = meld(hq[i], hq[hq_last]);
	i++; hq_last--;
	}
    }
init_hq();
return(hq[0]);
}

/****************************************************************/
/*	Heap Melding.
/****************************************************************/
EDGE_PTR meld(h1, h2)
EDGE_PTR h1,h2;
{
    debug("meld",h1,h2);
    if (h1==NYL) return(h2);
    if (h2==NYL) return(h1);
    return(mesh(h1,h2));
}

EDGE_PTR mesh(h1,h2)
EDGE_PTR h1,h2;
{
    register EDGE_PTR h, rt1, lt1;
    debug("mesh",h1,h2);
    if (LENGTH(h1) > LENGTH(h2)) { h = h1; h1 = h2; h2 = h; }

    rt1 = RSON(h1);
    if (rt1==NYL) rt1 = h2;
    else rt1 = mesh(rt1, h2);

    lt1 = LSON(h1);
    if (RANK(lt1) < RANK(rt1)) {
	LSON(h1) = rt1; rt1 = lt1; 	/* swap right & left */
	}

    RANK(h1) = 1 + RANK(rt1);
    RSON(h1) = rt1;
    return(h1);
}


/****************************************************************/
/*	Lazy Melding.  Creates a dummy heap node.
/****************************************************************/
EDGE_PTR lazymeld(h1, h2, dummy)
EDGE_PTR h1, h2;
VERTEX_PTR dummy;
{
    register EDGE_PTR h;
    debug("lazymeld",h1,h2);
    if (RANK(h1) < RANK(h2)) {
	h = h1; h1 = h2; h2 = h;
	}
    h = alloc_edge();
    LSON(h) = h1;
    RSON(h) = h2;
    RANK(h) = 1 + RANK(h2);
    orig(h) = dest(h) = dummy;
    return(h);
}

/****************************************************************/
/* 	Purging a heap.  Removes dummy nodes near root.
/*	Puts real nodes on the heapfication queue.
/****************************************************************/
purge(h,v)
EDGE_PTR h;
VERTEX_PTR v;
{
    while ((h != NYL) && (find(dest(h)) == v)) {
	purge(RSON(h), v);
	h = LSON(h);
	}
    if (h != NYL) insert_hq(h);
/*    
    if (h != NYL) {
	if (find(dest(h)) == v) {  /* edge is deleted 
	    purge(LSON(h),v); purge(RSON(h),v);
	}
	else insert_hq(h);
    }
*/
}


/****************************************************************/
/*	Top-level MST procedure.
/****************************************************************/
#define findmin(h,v)	((purge((h),(v)), heapify_hq()))

build_min_span_tree(edge, size)
EDGE_PTR edge;
VERTEX_PTR size;
{
register EDGE_PTR i, j, k, min_edge;
register VERTEX_PTR vp_last, v;
double dx, dy;
/* 
fprintf(stderr,"build_min_span_tree(%d,%d)\n", edge, size); fflush(stderr);
*/

/*  Initialize father and heap pointers for each vertex. */
init_hq();
for (i = 1; i <= size; i++) {
    COUNT(i) = 0;
    FATHER(i) = i;
    HEAP(i) = NYL;
    }

/*  Mark edges on free list to be ignored later. */
for (i=avail_edge; i != NYL; i= onext(i)) {
    orig(i) = 0;
    dest(i) = 0;
    }
avail_edge = NYL;

/*  Compute and save length of every DT edge. */
for (i=0; i<next_edge; i+=4) {
    dx = (X(orig(i)) - X(dest(i)));
    dy = (Y(orig(i)) - Y(dest(i)));
    LENGTH(i) = (dx * dx) + (dy * dy);
}	

/*  Construct initial heap of edges from each vertex. */
for (i=0; i<next_edge; i+=2) {
if ((HEAP(orig(i)) == NYL) && (orig(i) != dest(i))) {
    j = i;
    do {
	k = onext(j);
	LSON(j) = RSON(j) = NYL;
	RANK(j) = 0;
	insert_hq(j);
	j = k;
    } while (j != i);
    HEAP(orig(i)) = heapify_hq();
}
}

/*  Round-Robin merging of trees. */
vp_last = size;
while (TRUE) {
    j = 0;
    for (i=1; i<=vp_last; i++) {
	v = vp[i];
	if (v == FATHER(v)) {
	    min_edge = findmin(HEAP(v),v);
	    if (min_edge == NYL) {
		return;
	    } 
	    plot_mst_edge(min_edge);
	    debug("plot", min_edge, min_edge);
	    HEAP(v) = lazymeld(min_edge, HEAP(FATHER(dest(min_edge))), v);
	    FATHER(FATHER(dest(min_edge))) = v; /* set union */
	    vp[++j] = v;
	}
    }
    vp_last = j;
/*  fprintf(stderr,"vp_last = %d\n",vp_last); fflush(stderr); */
}
}

/****************************************************************/
/*	Output routine.
/****************************************************************/
plot_mst_edge(e)
EDGE_PTR e;
{
    COUNT(orig(e))++; COUNT(dest(e))++;
#ifdef POSTSCRIPT
	printf("p%d p%d drawseg\n", orig(e), dest(e));
#endif
}

dumpedge(e) EDGE_PTR e;
{
fprintf(stderr, " %d -> %d (%d,%lf) ", orig(e), dest(e), e,LENGTH(e));
if (LENGTH(10)< 0.1) fprintf(stderr,"*****");
}

/****************************************************************/
/*	Driver
/****************************************************************/
main(argc,argv)
int argc;
char *argv[];
{
register EDGE_PTR e;
EDGE_PTR rowe, top, bot, left, right;
EDGE_PTR edge;
int i,n,j,k, rows, lo, hi, m, x,y, seed;
double xx, yy, curmax;
char prog;

/* Parse command line. */
prog = *argv[0];

if ((prog == 'd') || (prog == 'g')) {
/*  plot_dt_construction =  (n<=342) */
    plot_dt_construction = FALSE;
    plot_colorful_dt = TRUE;
    }
else {
    plot_dt_construction = FALSE;
    plot_colorful_dt = FALSE;
    }

/* Check reasonableness of n and allocate large arrays. */
n=65534;
va = (struct VERTEX*) malloc((n+2)*sizeof(struct VERTEX));
vp = (VERTEX_PTR*) malloc((n+2)*sizeof(VERTEX_PTR));
org = (VERTEX_PTR*) malloc(16*n*sizeof(VERTEX_PTR)); 
		/* 12 ok except for mst*/
len = (double *) malloc(3*n*sizeof(double));
color = (int *) len;
hq = (EDGE_PTR*) malloc(n*sizeof(EDGE_PTR));
next = (EDGE_PTR*) malloc(16*n*sizeof(EDGE_PTR)); /* 12 */
/* next's is the largest allocation.  If any failed, that one did. */
if (next == NULL) { fprintf(stderr,"Memory allocation failed.\n"); return;}


#ifdef POSTSCRIPT
printf("%%!\n");
printf("%%Title:\n");
printf("/drawseg {moveto lineto stroke} def\n");
printf("/drawline {moveto lineto stroke} def\n");
printf("/drawsite {0.002 0 360 arc fill} def\n");
printf("3 72 mul dup scale\n");
printf("1.0 1.5 translate\n");
printf("0 setlinecap\n");
printf("2 setlinejoin\n");
printf("0.003  setlinewidth\n");
printf("[ ] 0 setdash\n");
#endif

/*while (TRUE)*/ {

    i=1;
    while (scanf("%lf %lf\n", &(X(i)), &(Y(i)))==2) {
	  vp[i] = i; 
	  NORM(i) = X(i)*X(i) + Y(i)*Y(i);
	  i++;
	}

    n=i-1;
    vp[0] = 0; vp[n+1] = n+1;    /* sentinals for sorting routines */
	vpsortx(1,n);
    delete_all_edges();
    if (prog == 'g')
	build_delaunay(vp, 1, n, &left, &right, n);
    else if (prog != 'c')
	build_delaunay(vp, 1, n, &left, &right, 
	    (int) (0.5 + sqrt((double) n / log((double) n)))); 
#ifdef POSTSCRIPT
    for (i=1; i<=n; i++) {
	  printf("/p%0d {%lf %lf} def ", i, X(i), Y(i));
	  plot_site(i);
#endif
	}
    switch (prog) {
	case 'm':
	    output_voronoi_diagram(left, right); 
/*	    output_delaunay_triangulation(left, right);  */
	    build_min_span_tree(left, n);
	    break;
	case 'v': 
	    output_voronoi_diagram(left, right); 
	    break;
	case 'd': case 'g':
	    output_colorful_delaunay_triangulation(left, right);
	    break;
	    }
    }
}
