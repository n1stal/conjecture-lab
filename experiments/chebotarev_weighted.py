import numpy as np
from scipy.optimize import minimize
def lap(A):
 return A.sum(axis=-1)[...,None]*np.eye(A.shape[-1])-A

def tour(n):
 u,v=np.triu_indices(n,1)
 B=np.arange(1<<len(u),dtype=np.int64)
 best=-1
 for ix in range(0,len(B),8192):
  m=B[ix:ix+8192]
  x=((m[:,None]>>np.arange(len(u)))&1).astype(float)
  A=np.zeros((len(m),n,n))
  A[:,u,v]=x;A[:,v,u]=1-x
  vals=np.max(np.linalg.eigvals(lap(A)).imag,axis=-1)/n
  yi=vals.argmax()
  if vals[yi]>best: best=vals[yi]; M=A[yi]
 return best,M

rng=np.random.default_rng(26)
for n in (6,8,10,12,16):
 A=np.zeros((n,n)); i=np.arange(n)
 for d in range(1,n//2): A[i,(i+d)%n]=1
 ij=np.where(~np.eye(n,dtype=bool))
 f=lambda X:np.linalg.eigvals(lap(X)).imag.max()/n
 def opt(x):
  def obj(z):
   T=np.zeros((n,n));T[ij]=z
   return -f(T)
  return minimize(obj,x[ij],method='L-BFGS-B',bounds=[(0,1)]*len(ij[0]),options={'maxiter':100,'ftol':1e-10})
 best=f(A)
 print('START',n,best, np.cos(np.pi/n)/np.sin(np.pi/n)/n,flush=True)
 if n<=6:
  v,T=tour(n); print('TOURNAMENT',n,v,T.tolist(),flush=True)
  if v>best: best=v
 for k in range(100):
  j=k%3
  if j==0:
   X=A.copy();mask=rng.uniform(0,1,(n,n))<rng.uniform(0,.5);X[mask]=rng.uniform(0,1,mask.sum())
  elif j==1:
   X=rng.beta(.3,.3,(n,n))
  else:
   X=A.copy()
   for a in range(n//2): X[a,a+n//2]=rng.uniform(0,1);X[a+n//2,a]=rng.uniform(0,1)
  res=opt(X)
  if -res.fun>best+1e-9:
   best=-res.fun
   T=np.zeros((n,n));T[ij]=res.x
   print('IMPROVED',n,k,best,T.tolist(),flush=True)
 print('END',n,best,flush=True)
