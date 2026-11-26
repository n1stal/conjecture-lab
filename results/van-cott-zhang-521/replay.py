from itertools import combinations_with_replacement

def system(n):
    if n == 11:
        return [1,2,4,5,7,9,12,14,17,22,27]  # Van Cott–Zhang, §5
    if n == 12:
        return [1,2,4,5,7,8,10,11,13,16,19,22]
    if n == 14:
        return [1,2,4,5,7,8,10,13,15,18,21,26,29,37]
    assert n == 13 or n >= 15
    L = 3*n-17
    return sorted([*range(1,L+1,3),2,5,8,14,L+6])

def greedy(a, v):
    length = 0
    for c in reversed(a):
        q, v = divmod(v,c)
        length += q
    return length

def differences_dp(a):
    if len(a) < 3:
        return []
    # Kozen–Zaks: if non-canonical then some failure below c[-2]+c[-1].
    opt = [0]
    out = []
    for v in range(1,a[-2]+a[-1]):
        opt.append(1+min(opt[v-c] for c in a if c <= v))
        if greedy(a,v) > opt[v]:
            out.append(v)
    return out

for n in range(11,76):
    C = system(n)
    assert len(C) == n and sorted(set(C)) == C and C[0] == 1
    assert not differences_dp(C[:3]) and not differences_dp(C)
    for i in range(4,n):
        assert differences_dp(C[:i]), (n,i)
    if n in [11,12,13,14,15,16,17]:
        print(n, C, [differences_dp(C[:i])[0] for i in range(4,n)])
print("All lengths 11–75 passed the independent finite DP replay, not used by the parametric proof.")
