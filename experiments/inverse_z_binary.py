"""Exact inverse Z-polynomial experiments for binary matroids.

Uses the flat-lattice recurrence of https://arxiv.org/html/2510.01086v2,
Theorem 2.2. The optional cross-check instead inverts the ordinary
Z-polynomials in the incidence algebra.
"""
from itertools import combinations
from random import Random
from math import comb
from functools import lru_cache
from fractions import Fraction
import argparse

def bits(mask):
    while mask:
        b=mask&-mask
        yield b.bit_length()-1
        mask-=b

@lru_cache(maxsize=120000)
def new_span(span,v):
    return span | sum(1<<(u^v) for u in bits(span))

def flats(points):
    ground=sum(1<<v for v in points)
    seen={1}; togo=[(1,0)]; rank={}
    for span,r in togo:
        mask=span&ground
        assert mask not in rank
        rank[mask]=r
        for v in bits(ground & ~span):
            s=new_span(span,v)
            if s not in seen:
                seen.add(s)
                togo.append((s,r+1))
    return tuple(rank),tuple(rank.values())

def inverse_z(fs, ranks, crosscheck=False):
    n=len(fs)
    below=[tuple(j for j in range(i) if fs[j]&~f==0) for i,f in enumerate(fs)]
    q=[]; y=None
    for i in range(n):
        b=below[i]; k=ranks[i]
        col={i:1}
        for j in reversed(b):
            col[j]=-sum(v for a,v in col.items() if fs[j]&~fs[a]==0)
        y=[0]*(k+1)
        for j in b:
            d=k-ranks[j]
            factor=(-1)**d * col[j]
            for ell,c in enumerate(q[j]):
                y[d+ell]+=factor*c
        qi=tuple(y[k-ell]-y[ell] for ell in range((k+1)//2)) if k else (1,)
        for ell,c in enumerate(qi): y[ell]+=c
        q.append(qi)
        assert y==y[::-1] and all(c>0 for c in y),(fs[i],y)
    if crosscheck:
        assert tuple(y)==by_inverse(fs,ranks,below)
    return tuple(y)

def by_inverse(fs,ranks,below):
    # Build ordinary Z polynomials from contractions, then invert in the incidence algebra.
    p={}; z={}
    for i in range(len(fs)):
        for j in (i,*reversed(below[i])):
            k=ranks[i]-ranks[j]
            t=[0]*(k+1)
            if i==j:
                p[j,i]=(1,); z[j,i]=(1,); continue
            for a in (*below[i],i):
                if a!=j and fs[j]&~fs[a]==0:
                    for ell,c in enumerate(p[a,i]):
                        t[ranks[a]-ranks[j]+ell]+=c
            pi=tuple(t[k-ell]-t[ell] for ell in range((k+1)//2))
            for ell,c in enumerate(pi): t[ell]+=c
            p[j,i]=pi; z[j,i]=tuple(t)
            assert t==t[::-1]
    y=[(1,)]
    for i in range(1,len(fs)):
        k=ranks[i]
        acc=[0]*(k+1)
        for j in below[i]:
            for a,x in enumerate(y[j]):
                for b,t in enumerate(z[j,i]):
                    acc[a+b]-=x*t
        y.append(tuple(acc))
    return tuple((-1)**ranks[-1]*c for c in y[-1])

def rank4_formula(fs, ranks):
    points, lines, planes = ([f for f,r in zip(fs,ranks) if r==k] for k in (1,2,3))
    w1,w2,w3=map(len,(points,lines,planes))
    i12=sum(line.bit_count() for line in lines)
    i13=sum(plane.bit_count() for plane in planes)
    heights=[sum(line&~plane==0 for plane in planes) for line in lines]
    i23=sum(heights)
    t=sum(line.bit_count()*height for line,height in zip(lines,heights))
    a=t-i23-i13+w3-i12+w2+w1-1
    b=t-i13-i12+w1
    c=t-i12+w2-i13
    assert b-a-(c-b) >= w1-3
    return a,b,c,b,a

def check(points,crosscheck=False):
    fs,rs=flats(points)
    y=inverse_z(fs,rs,crosscheck)
    if rs[-1]==4:
        assert y==rank4_formula(fs,rs), (points,y)
    ratios=[Fraction(y[i]**2,y[i-1]*y[i+1]) for i in range(1,len(y)-1)]
    return rs[-1],y,min(ratios,default=Fraction(10)),len(fs)

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--trials',type=int,default=300)
    p.add_argument('--seed',type=int,default=117)
    p.add_argument('--rank4-all',action='store_true')
    a=p.parse_args()
    assert check([1,2,4,8],True)[1]==tuple(comb(4,i) for i in range(5))
    assert check([1,2,3],True)[1]==(2,3,2)
    for r0 in (3,4,5):
        y=check(list(range(1,2**r0)),True)[1]
        expected=[2**(i*(i-1)//2+(r0-i)*(r0-i-1)//2) for i in range(r0+1)]
        # Gaussian binomial [r0 choose i]_2
        for i in range(r0+1):
            for j in range(i):
                expected[i] *= (2**(r0-j)-1)
            for j in range(i):
                expected[i] //= (2**(i-j)-1)
        assert tuple(expected)==y,(y,expected)
    rng=Random(a.seed); best={}; counts={}
    samples=([*bits(m)] for m in range(2,1<<16,2)) if a.rank4_all else (
        rng.sample(range(1,2**r),rng.randrange(r,min(2**r,3*r+1)))
        for r in (4,5,6) for _ in range(a.trials))
    for i,points in enumerate(samples):
        r,y,v,n=check(points,i<10)
        counts[r]=counts.get(r,0)+1
        if r not in best or v<best[r][0]:
            best[r]=(v,points,y,n)
        if v<1:
            assert check(points,True)[2]==v
            print('COUNTEREXAMPLE',r,points,y,v,flush=True)
            break
    print('counts:',counts,flush=True)
    for r,row in sorted(best.items()):
        print('near-min:',r,row,flush=True)
