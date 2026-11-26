"""Exact non-horizontal slant certification for 6-vertex unweighted spectrum."""
from math import comb
from chebotarev_verify6 import newton
import sys
D=25
def cmul(u,v):
    a,b=u;c,d=v
    return (a*c-3*b*d,a*d+b*c)
def scheme(a,b,cap):
    w=[(1,0)]
    for _ in range(D):w.append(cmul(w[-1],(a,b)))
    mul=[]
    for k in range(D+1):
        row=[]
        for j in range(k//2+1):
            sign=1 if 2*j==k else 2
            mij=cmul(w[j],(w[k-j][0],-w[k-j][1]))[0]
            v=sign*comb(k,j)*mij
            if v:row.append((j,v))
        mul.append(row)
    shift=[[(j,comb(k,j)*(-2*cap)**(k-j)) for j in range(k+1)] for k in range(D+1)]
    return mul,shift

tests=[scheme(-3,-1,0),scheme(-1,-1,1),scheme(1,-1,7),scheme(3,-1,18)]
def verify(p,scheme):
    mul,shift=scheme
    q=[sum(v*p[j]*p[k-j] for j,v in row) for k,row in enumerate(mul)]
    s=[sum(a*q[j] for j,a in row) for row in shift]
    C=[1]
    for m in range(1,D+1):
        a=-sum(C[m-j]*s[j] for j in range(1,m+1))
        if a<0:return False
        assert a%m==0
        C.append(a//m)
    return True
def main():
    edge = newton([1,-6,0,0,0,0],D)  # roots 0 and 6: polygon vertices
    assert all(verify(edge,t) for t in tests)
    outside = newton([1,-7,0,0,0,0],D)
    assert not verify(outside,tests[-1])
    nonreal_outside = newton([1,0,4,0,0,0],D)  # a root at +2i
    assert not verify(nonreal_outside,tests[1])
    n=0
    for line in sys.stdin:
        c=list(map(int,line.split()))
        p=newton(c,D)
        assert all(verify(p,t) for t in tests),c
        n+=1
    assert n==44729,n
    print(f'Verified all four pairs of slanted edges on {n} characteristic polynomials.')
if __name__=='__main__':main()
