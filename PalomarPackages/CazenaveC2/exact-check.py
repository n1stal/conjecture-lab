#!/usr/bin/env python3
"""Exact arithmetic regression for the two-diamond Cazenave #20829 refutation."""
from fractions import Fraction as Q
from itertools import product
import sys

def build(k):
    assert k >= 3
    n=8+k
    diamond=((0,1),(0,2),(1,2),(1,3),(2,3))
    path=(0,*range(8,n),4)
    edges=diamond+tuple((a+4,b+4) for a,b in diamond)+tuple(zip(path,path[1:]))
    A=[[0]*n for _ in range(n)]
    for u,v in edges:
        assert u != v and A[u][v] == 0
        A[u][v]=A[v][u]=1
    return A,edges

def pd_pivots(S):
    B=list(map(list,S)); n=len(B); D=[]
    for p in range(n):
        d=B[p][p]
        assert d>0, (p,d)
        D.append(d)
        for i in range(p+1,n):
            for j in range(i,n):
                B[i][j] -= B[p][i]*B[p][j]/d
                B[j][i]=B[i][j]
    return D

def det(S):
    ans=Q(1)
    for p in pd_pivots(S): ans*=p
    return ans

def qf(A,u,v): return sum(A[i][j]*u[i]*v[j] for i,j in product(range(len(A)),repeat=2))

def check(k):
    A,edges=build(k); n=len(A); ds=list(map(sum,A)); T=Q(37,8)
    reached={0}
    for _ in range(n):
        reached.update(j for i in tuple(reached) for j in range(n) if A[i][j])
    assert len(reached)==n and max(ds)==3
    B=[[T-ds[i] if i==j else Q(A[i][j]) for j in range(n)] for i in range(n)]
    pd_pivots(B)
    C=[row[:4] for row in B[:4]]
    minors=[det([row[:i] for row in C[:i]]) for i in range(1,5)]
    assert minors==[Q(13,8),Q(105,64),Q(725,512),Q(6905,4096)]
    g=det([row[1:] for row in C[1:]])/minors[-1]
    x=T-2-g; y=T-2
    assert g==Q(2504,1381) and x==Q(8969,11048)
    assert x*y-2==Q(11581,88384) and 0<x<1 and y-1/x>1 and y>2
    u=[0]*n; v=[0]*n
    for row,ids in ((u,(0,1,2,3,8)),(v,(4,5,6,7,n-1))):
        for i,h in zip(ids,(10,11,11,8,4)): row[i]=h
    assert sum(i*j for i,j in zip(u,v))==qf(A,u,v)==0
    assert qf(A,u,u)==qf(A,v,v)==1114
    assert sum(i*i for i in u)==sum(i*i for i in v)==422
    assert Q(1114,422)-Q(21,8)==Q(25,1688)>0
    return n,edges

if __name__=='__main__':
    cases=list(range(3,33))
    if sys.argv[1:]: cases=list(map(int,sys.argv[1:]))
    for k in cases: check(k)
    n,e=check(3)
    print(f'Exact positive-definiteness and two-dimensional Rayleigh checks: {len(cases)} family members')
    print(f'11-vertex witness: {e}')
    print('No floating-point or numerical-eigenvalue decisions.')
