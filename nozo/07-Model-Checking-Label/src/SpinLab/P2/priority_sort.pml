#define N	11

int nn[N] = { 8, 9, 4, 3, 3, 6, 7, 4, 1, 9, 3 }
int prset

chan nrs = [N] of { int }

proctype prnr(int n)
{
	_priority = n -> prset++
	(prset == N)  -> nrs!n
}

init {
	int i, n;
	
	for (i : 1 .. N) {
		run prnr( nn[i-1] )
	}
	len(nrs) == N
	for (i : 1 .. N) {
		nrs?n
		nn[N-i] = n
	}
	for (i : 1 .. N) {
		printf("%d,", nn[i-1])
	}
	printf("\n")
}
