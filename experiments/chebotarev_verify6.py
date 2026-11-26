"""Verify the height bound from a stream of exact quotient characteristic polynomials."""
from math import comb
import sys

def newton(c, j):
    """Power sums p[0..j] for the roots of a monic polynomial with coefficients c."""
    n=len(c)-1
    p=[n]
    for m in range(1,j+1):
        if m<=n: p.append(-m*c[m]-sum(c[i]*p[m-i] for i in range(1,m)))
        else: p.append(-sum(c[i]*p[m-i] for i in range(1,n+1)))
    return p

def verified(c):
    n=len(c)-1; D=comb(n,2)
    p=newton(c,2*D)
    q=[D]
    for k in range(1,D+1):
        q2=sum((-1)**i*comb(2*k,i)*p[i]*p[2*k-i] for i in range(2*k+1))
        assert q2%2==0
        q.append(q2//2)
    s=[(-1)**k*sum(comb(k,j)*12**(k-j)*q[j] for j in range(k+1)) for k in range(D+1)]
    C=[1]
    for m in range(1,D+1):
        a=-sum(C[m-k]*s[k] for k in range(1,m+1))
        assert a%m==0
        C.append(a//m)
    return all(t>=0 for t in C)

def main():
    assert verified([1,0])
    assert verified([1,0,3])
    assert not verified([1,0,4])
    assert verified([1,-2,4])
    n=0
    for line in sys.stdin:
        c=list(map(int,line.split()))
        assert len(c)==6 and c[0]==1
        assert verified(c),f"height violation: {c}"
        n+=1
    assert n == 44_729, f"incomplete or unexpected spectrum census: {n}"
    print(f"Verified nonnegative strip-test coefficients for {n} characteristic polynomials.")
if __name__=="__main__":main()
