"""Enumerate all 6-vertex unweighted digraph spectra up to skeleton relabeling/complements.

NumPy screening, not an exact certificate; exhaustive refers to graph coverage.
"""
from itertools import combinations, permutations
import numpy as np

n=6
pairs=list(combinations(range(n),2))
idx={e:i for i,e in enumerate(pairs)}
pm=np.array([[1<<idx[tuple(sorted((p[u],p[v])))] for u,v in pairs] for p in permutations(range(n))],dtype=np.int32)
marked=np.zeros(1<<len(pairs),dtype=bool)
skeletons=[]
for mask in range(len(marked)):
    if marked[mask]: continue
    es=[j for j in range(len(pairs)) if mask>>j&1]
    skeletons.append([pairs[j] for j in es])
    marked[pm[:,es].sum(axis=1,dtype=np.int32)]=True
assert len(skeletons)==156 and marked.all()
eye=np.eye(n)
best=(-1.,None,None)
best_polygon=(-1.,None,None)
count=0
t=2*np.pi/n
lam=np.r_[0,np.cumsum((1-np.exp(-1j*t*np.arange(1,n)))/n)]
assert np.allclose(lam[-1],1.)
poly=np.r_[lam, np.conj(lam[-2:0:-1])]
edges=np.roll(poly,-1)-poly
assert len(edges)==2*(n-1)
mid=.5+.0j
s=np.sign(((mid-poly)*np.conj(edges)).imag)
for m,E in sorted((len(E),E) for E in skeletons):
    U,V=np.array(E,dtype=int).reshape(m,2).T
    for k in range(min(m,15-m)+1):
        for D in combinations(range(m),k):
            DD=set(D)
            free=[j for j in range(m) if j not in DD]
            for ix in range(0,1<<len(free),16384):
                x=((np.arange(ix,min(1<<len(free),ix+16384),dtype=np.uint32)[:,None]>>np.arange(len(free),dtype=np.uint32))&1).astype(np.float64)
                arrays=np.zeros((len(x),n,n))
                arrays[:,U[free],V[free]]=x;arrays[:,V[free],U[free]]=1-x
                arrays[:,U[list(D)],V[list(D)]]=1;arrays[:,V[list(D)],U[list(D)]]=1
                eig=np.linalg.eigvals(arrays.sum(axis=-1)[...,None]*eye-arrays)/n
                vals=eig.imag.max(axis=1)
                a=int(vals.argmax())
                if vals[a]>best[0]: best=(vals[a],arrays[a].astype(int).tolist(),eig[a].tolist())
                vals2=(((eig[:,:,None]-poly[None,None,:])*np.conj(edges)[None,None,:]).imag*(-s/np.abs(edges))[None,None,:]).max(axis=(1,2))
                b=int(vals2.argmax())
                if vals2[b]>best_polygon[0]: best_polygon=(vals2[b],arrays[b].astype(int).tolist(),eig[b].tolist())
                count+=len(x)
print('skeletons',len(skeletons),'digraph representatives with repetitions',count)
print('baseline',1/(n*np.tan(np.pi/n)))
print('max_imag',best)
print('max_polygon_signed_distance',best_polygon)
