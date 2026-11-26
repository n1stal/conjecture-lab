#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <limits>
#include <set>
#include <vector>

using Coeff = std::array<int,6>;
using Ed = std::pair<int,int>;
static_assert(std::numeric_limits<int>::digits >= 31);
std::vector<Ed> pairs;
std::set<Coeff> polys;
uint64_t count=0;
int A[6][6]{};
int L[6][6]{};
void cert_charpoly(){
  int Q[5][5], M[5][5], next[5][5], tr[6]{};
  for(int i=0;i<6;++i){
    int d=0;
    for(int j=0;j<6;++j){ L[i][j]=-A[i][j];d+=A[i][j];}
    L[i][i]=d;
  }
  for(int i=0;i<5;++i) for(int j=0;j<5;++j) Q[i][j]=M[i][j]=L[i][j]-L[5][j];
  for(int k=1;k<=5;++k){
    for(int i=0;i<5;++i)tr[k]+=M[i][i];
    if(k==5)break;
    for(int i=0;i<5;++i) for(int j=0;j<5;++j){
      int s=0;
      for(int h=0;h<5;++h)s+=M[i][h]*Q[h][j];
      next[i][j]=s;
    }
    for(int i=0;i<5;++i)for(int j=0;j<5;++j)M[i][j]=next[i][j];
  }
  Coeff c{1,0,0,0,0,0};
  for(int k=1;k<=5;++k){
    int s=0;for(int j=1;j<=k;++j)s+=tr[j]*c[k-j];
    assert(s%k==0);
    c[k]=-s/k;
  }
  polys.insert(c);++count;
}
void directs(const std::vector<Ed> &E,int k,int bonus){
  if(k==static_cast<int>(E.size())){cert_charpoly();return;}
  auto [u,v]=E[k];
  A[u][v]=1;directs(E,k+1,bonus);
  A[u][v]=0;A[v][u]=1;directs(E,k+1,bonus);
  if(bonus){A[u][v]=1;directs(E,k+1,bonus-1);A[u][v]=0;}
  A[v][u]=0;
}
int main(){
  int index[6][6]{};
  for(int a=0;a<6;++a)for(int b=a+1;b<6;++b){
    index[a][b]=index[b][a]=pairs.size();pairs.emplace_back(a,b);
  }
  std::array<int,6> p{0,1,2,3,4,5};
  std::vector<std::array<int,15>> permutations;
  do{
    std::array<int,15> bits{};
    for(int i=0;i<15;++i){auto [u,v]=pairs[i];bits[i]=1<<index[p[u]][p[v]];}
    permutations.push_back(bits);
  }while(std::next_permutation(p.begin(),p.end()));
  std::array<bool,1<<15> seen{};
  int classes=0;
  for(int mask=0; mask<(1<<15); ++mask){
    if(seen[mask])continue;
    ++classes;
    std::vector<Ed>E;
    std::vector<int>R;
    for(int i=0;i<15;++i)if(mask>>i&1){E.push_back(pairs[i]);R.push_back(i);}
    for(const auto &bits:permutations){
      int m=0;for(const auto i:R)m|=bits[i];seen[m]=true;
    }
    directs(E,0,15-static_cast<int>(E.size()));
  }
  assert(classes==156);assert(count==4241864);
  std::cerr<<"Representatives: "<<count<<", distinct quotient characteristic polynomials: "<<polys.size()<<'\n';
  for(const auto &c:polys){
    for(int i=0;i<6;++i)std::cout<<c[i]<<(i==5?'\n':' ');
  }
}
