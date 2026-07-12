#include<bits/stdc++.h>
#include<ext/pb_ds/assoc_container.hpp>
using namespace std;
using namespace __gnu_pbds;
#define ordered_set tree<int, null_type, less<int>, rb_tree_tag, tree_order_statistics_node_update>
#define ll long long
#define ull unsigned long long
#define ld long double
#define vi vector<int>
#define vull vector<ull>
#define pb push_back
#define pf push_front
#define vll vector<ll>
#define vvi vector<vector<int>>
#define vvll vector<vector<ll>>
#define L(i,j,k) for(int i=(j);i<=(k);++i)
#define R(i,j,k) for(int i=(j);i>=(k);i--)
#define Lll(i,j,k) for(ll i=(j);i<=(k);i++)
#define Rll(i,j,k) for(ll i=(j);i>=(k);i--)
#define forcin(arr) for(auto &i:arr) cin>>i;
#define all(arr) arr.begin(),arr.end()
mt19937 Rng(chrono::steady_clock::now().time_since_epoch().count());
constexpr ll infll=4e18;
constexpr ll inf=4e18;
#define F first
#define S second
#define int ll
using pii=pair<int,int>;
using pll=pair<ll,ll>;
const int maxn=2e6+5;
const int maxn1=3e5+5;
const ll mod=998244353;
const ll mod1=1e9+7;
const ll modi1=1e9+21;
const ll modi2=1e9+27;
const double mpii=acos(-1);
//#define arr array<int,2>
 
long long binpow(long long a,long long b){
    long long ans=1;
    while(b>0){
        if(b&1)ans=ans*a;
        a=a*a;
        b>>=1;
    }
    return ans;
}
long long binpow(long long a,long long b,long long modx){
    long long ans=1;
    a%=modx;
    while(b>0){
        if(b&1)ans=(__int128)ans*a%modx;
        a=(__int128)a*a%modx;
        b>>=1;
    }
    return ans;
}
const int N=4e6+5;
ll fact[N],inv[N];
void precompute(ll modiis){
    fact[0]=1;
    L(i,1,N-1){
        fact[i]=fact[i-1]*i%modiis;
    }
    inv[N-1]=binpow(fact[N-1],modiis-2,modiis);
    R(i,N-2,0){
        inv[i]=inv[i+1]*(i+1)%modiis;
    }
}
ll comb(int n,int m){
    if(m<0||m>n) return 0;
    return fact[n]*(inv[m]%mod*inv[n-m]%mod)%mod;
}
ll perm(int n,int m){
    return (fact[n]%mod*inv[n-m]%mod)%mod;
}
 
ll ex_gcd(int a,int b,int &x,int &y){
    if(b==0){x=1;y=0;return a;}
    int x1,y1;
    int gc1=ex_gcd(b,a%b,x1,y1);
    x=y1;
    y=x1-(a/b)*y1;
    return gc1;
}
inline bool ispow2(ull x){
    return x and ((x &(x-1))==0);
}
#define int ll
struct BIT{
    int n; vi f;
    BIT(int n=0):n(n),f(n+1,0) {}
    void add(int i,ll val){
        for(;i<=n;i+=i&-i) {f[i]+=val;}
    } 
    int sum(int i){
        int s=0;
        for(;i>0;i-=i&-i){
            s+=f[i];
           
        }
        return s;
    }
    int sum(int l,int r){
        if(r<l) return 0;
        return (sum(r)-sum(l-1));
    }
};
using cd=complex<double>;
const int rooti=3;
const int maxsize=1<<21;
class polynomial{
private:
  vi rev;
void prevrev(int n){
    int logn=0;
    while((1<<logn)<n) logn++;
    rev.resize(n);
    rev[0]=0;
    L(i,1,n-1){
        rev[i]=(rev[i>>1]>>1)|((i&1)<<(logn-1));
    }
}
void fft(vector<cd> &a,bool inv){
    int n=(int)a.size();
    L(i,1,n-1){
        if(i<rev[i]) swap(a[i],a[rev[i]]);
    }
    for(int len=2;len<=n;len<<=1){
        double angle=2*mpii/len*(inv?-1:1);
        cd wlen(cos(angle),sin(angle));
        for(int i=0;i<n;i+=len){
            cd w(1);
            for(int j=0;j<len/2;j++){
            cd u=a[i+j],v=a[i+j+len/2]*w;
            a[i+j]=u+v;
            a[i+j+len/2]=u-v;
            w*=wlen;
        }
      }
    }
    if(inv){
        for(cd &x:a){
            x/=n;
        }
    }
}
void ntt(vll&a,bool inv){
    int n=a.size();
    for(int i=0;i<n;i++){
        if(i<rev[i]) swap(a[i],a[rev[i]]);
    }
    for(int l=2;l<=n;l<<=1){
        ll w=binpow(rooti,(mod-1)/l,mod);
        if(inv)w=binpow(w,mod-2,mod);
        for(int i=0;i<n;i+=l){
            ll wn=1;
            L(j,0,l/2-1){
                ll u=a[i+j],v=a[i+j+l/2]*wn%mod;
                a[i+j]=(u+v)%mod;
                a[i+j+l/2]=(u-v+mod)%mod;
                wn=wn*w%mod;
            }
        }
    }
    if(inv){
        ll ni=binpow(n,mod-2,mod);
        for(ll&x:a)x=x*ni%mod;
    }
}
public:
 polynomial(){}
 vector<double> mulfft(vector<double> a,vector<double> b){
     vector<cd> fa(all(a)),fb(all(b));
     int n=1;
     int na=a.size(),nb=b.size();
     while(n<na+nb-1) n<<=1;
     fa.resize(n);fb.resize(n);
     prevrev(n);
     fft(fa,0);
     fft(fb,0);
     L(i,0,n-1){
         fa[i]*=fb[i];
     }
     fft(fa,1);
     vector<double> res(na+nb-1);
     L(i,0,na+nb-2){
         res[i]=llround(fa[i].real());
     }
     return res;
 }
vll mulntt(vll a,vll b){
    int s=1;
    while(s<(int)(a.size()+b.size()))s<<=1;
    a.resize(s);b.resize(s);
    ntt(a,0);ntt(b,0);
    L(i,0,s-1)a[i]=a[i]*b[i]%mod;
    ntt(a,1);
    return a;
}
};
struct querymo{
    int l,r,id;
};
inline int readInt(){
    int x=0;
    char c=getchar();
    while(c<'0'||c>'9') c=getchar();
    while(c>='0' && c<='9'){
        x=x*10+c-'0';
        c=getchar();
    }
    return x;
}
const int maxni1=5e5+6;
const int maxmi=805;
//#define int ll
vi z_function(const string &s){
    int n=s.length();
    vi z(n);
    for(int i=1,l=0,r=0;i<n;i++){
        if(i<=r){
            z[i]=min(r-i+1,z[i-l]);
        }
        while(i+z[i]<n and s[z[i]]==s[i+z[i]]){
            ++z[i];
        }
        if(i+z[i]-1>r){
            l=i;
            r=i+z[i]-1;
        }
    }
    return z;
}
const int K=30;
struct basis{
    vi b;
    basis():b(K,0) {}
    void insert(int val){
        R(i,K-1,0){
            if(!(val & (1<<i))) continue;
            if(!b[i]){
                b[i]=val;
                return;
            }
            val^=b[i];
        }
    }
    int reduce(int val){
        R(i,K-1,0){
            val=min(val,val^b[i]);
        }
        return val;
    }
};
inline int qury(int l,int r){
   cout<<"? "<<l<<" "<<r<<endl;
   int x;cin>>x;
   return x;
}
vi maxnode(200005);
struct Dsu{
    ll n;
    vll par,sz;
    vll rel,c0,c1,forced;
    ll tot;
    Dsu(ll n=0):n(n),par(n+1),sz(n+1,1),rel(n+1,0),c0(n+1,0),c1(n+1,1),forced(n+1,-1),tot(0){iota(all(par),0);}
    ll find(ll x){
        return par[x]=(par[x]==x?x:find(par[x]));
    }
    pii find1(int x){
        if(par[x]==x) return {x,0};
        auto it=find1(par[x]);
        par[x]=it.F;
        rel[x]^=it.S;
        return {par[x],rel[x]};
    }
    bool unite(ll a,ll b){
        a=find(a),b=find(b);
        if(a==b) return 0;
        if(sz[a]<sz[b]) swap(a,b);
        par[b]=a;sz[a]+=sz[b];
        return 1;
    }
    void unitev(ll a,ll b){
        a=find(a);b=find(b);
        if(a!=b){
            if(sz[a]<sz[b]) swap(a,b);
            par[b]=a;
            sz[a]+=sz[b];
        }
    }
    int getc(int r){
        if(forced[r]==0) return c0[r];
        if(forced[r]==1) return c1[r];
        return min(c0[r],c1[r]);
    }
    bool unite1(int u,int v,int d){
        auto pu=find1(u),pv=(find1(v));
        if(pu.F==pv.F) return 0;
        int ru=pu.F,rv=pv.F;
        int reld=d^pu.S^pv.S;
        tot-=getc(ru);
        tot-=getc(rv);
        par[rv]=ru;
        rel[rv]=reld;
        if(reld==0){
            c0[ru]+=c0[rv];
            c1[ru]+=c1[rv];
            if(forced[rv]!=-1) forced[ru]=forced[rv];
        }
        else{
            c0[ru]+=c1[rv];
            c1[ru]+=c0[rv];
            if(forced[rv]!=-1) forced[ru]=forced[rv]^1;
        }
        tot+=getc(ru);
        return 1;
    }
    void unite1(int a,int b){
        a=find(a);b=find(b);
        if(a!=b){
            par[b]=a;
            maxnode[a]=max(maxnode[a],maxnode[b]);
        }
    }
    ll sizee(ll x) {
        return sz[find(x)];
    }
    void use(int x) {
        par[x]=find(x+1);
    }
    void force(int u,int st){
        auto pu=find1(u);
        int ru=pu.F;
        tot-=getc(ru);
        forced[ru]=st^pu.S;
        tot+=getc(ru);
    }
};   
vi piii(string p){
    int m=p.length();
    vi pi(m);
    int j=0;
    L(i,1,m-1){
        while(j>0 and p[i]!=p[j]){
            j=pi[j-1];
        }
        if(p[i]==p[j]) j++;
        pi[i]=j;
    }
    return pi;
}   
struct bigint{
    vector<int> d;
    bigint(ll n = 0) {
        if(!n) d.push_back(0);
        while(n) d.push_back(n%10),n/=10;
    }
    void trim() {
        while(d.size()>1 && !d.back()) d.pop_back(); 
    }
    bigint operator+(const bigint& o) const {
        bigint r; r.d.clear();
        int c = 0;
        for (int i = 0; i < max(d.size(), o.d.size()) || c; ++i) {
            int s = c + (i < d.size() ? d[i] : 0) + (i < o.d.size() ? o.d[i] : 0);
            r.d.push_back(s % 10); c = s / 10;
        }
        return r;
    }
    void operator+=(const bigint& o) { *this = *this + o; }
    void operator-=(const bigint& o) {
        int b = 0;
        for (int i = 0; i < o.d.size() || b; ++i) {
            int s = d[i] - b - (i < o.d.size() ? o.d[i] : 0);
            d[i] = (s < 0 ? s + 10 : s);
            b = (s < 0);
        }
        trim();
    }
    bigint operator*(const bigint& o) const {
        if (d.empty() || o.d.empty()) return 0;
        vector<int> r(d.size() + o.d.size(), 0);
        for (int i = 0; i < d.size(); ++i)
            for (int j = 0; j < o.d.size(); ++j)
                r[i + j] += d[i] * o.d[j];
        for (int i = 0; i < r.size() - 1; ++i)
            r[i + 1] += r[i] / 10, r[i] %= 10;
        bigint res; res.d = r; res.trim();
        return res;
    }
    void operator*=(const bigint& o) { *this = *this * o; }
    friend ostream& operator<<(ostream& os, const bigint& b) {
        if (b.d.empty()) return os << 0;
        for (int i = b.d.size() - 1; ~i; --i) os << b.d[i];
        return os;
    }
};
const int phi=1e9+7;
struct mat{
    int r,c;
    vvi m;
    mat(int r,int c):r(r),c(c),m(r,vi(c,0)){}
    mat operator*(const mat &o) const{
       mat ans(r,o.c);
       L(i,0,r-1){
        L(j,0,o.c-1){
            L(k,0,c-1){
              ans.m[i][j]=(ans.m[i][j]+1ll*m[i][k]*o.m[k][j])%phi;
            }
        }
       }
       return ans;
    }
};
mat powm(mat a,ll b){
    int sz=a.r;
    mat res(sz,sz);
    L(i,0,sz-1){
        res.m[i][i]=1;
    }
    while(b>0){
        if(b&1) res=res*a;
         a=a*a;
        b/=2;
    }
    return res;
}
 
const int n1=200005;
struct node{
    ll sum,mn,mx,lazy;
} tre[4*n1];
ll a[n1];
void pushup(int node){
    tre[node].sum=tre[2*node].sum+tre[2*node+1].sum;
    tre[node].mn=min(tre[2*node].mn,tre[2*node+1].mn);
    tre[node].mx=max(tre[2*node].mx,tre[2*node+1].mx);
}
void apply(int node,int l,int r, ll val){
    tre[node].sum=(r-l+1)*val;
    tre[node].mn=val;
    tre[node].mx=val;
    tre[node].lazy=val;
}
void pushd(int node,int l,int r){
    if(tre[node].lazy!=0){
        int mid=(l+(r-l)/2);
        apply(2*node,l,mid,tre[node].lazy);
        apply(2*node+1,mid+1,r,tre[node].lazy);
        tre[node].lazy=0;
    }
}
void build(int node,int l,int r){
    tre[node].lazy=0;
    if(l==r){
        tre[node].sum=a[l];
        tre[node].mn=a[l];
        tre[node].mx=a[l];
        return;
    }
    int mid=l+(r-l)/2;
    build(2*node,l,mid);
    build(2*node+1,mid+1,r);
    pushup(node);
}
void upd(int node,int l,int r,int ql,int qr,ll val){
    if(ql>r or qr<l or tre[node].mn>=val) return;
    if(ql<=l and r<=qr and tre[node].mx<=val){
        apply(node,l,r,val);
        return;
    }
    pushd(node,l,r);
    int mid=l+(r-l)/2;
    upd(2*node,l,mid,ql,qr,val);
    upd(2*node+1,mid+1,r,ql,qr,val);
    pushup(node);
}
int buy(int node,int l,int r,int ql,int qr,ll &coins){
    if(ql>r or qr<l or tre[node].mn>coins) return 0;
    if(ql<=l and r<=qr and tre[node].sum<=coins){
        coins-=tre[node].sum;
        return r-l+1;
    }
    if(l==r) return 0;
    pushd(node,l,r);
    int mid=(l+(r-l)/2);
    int res=buy(2*node,l,mid,ql,qr,coins);
    res+=buy(2*node+1,mid+1,r,ql,qr,coins);
    return res;
}
struct edge{
    ll to,cost,flow,rev;
};
vector<vector<edge>> adj;
vll level,ptr;
void adde(int u,int v,ll cost){
    adj[u].pb({v,cost,0,(ll)adj[v].size()});
    adj[v].pb({u,0,0,(ll)adj[u].size()});
}
bool bfs(int u,int v){
    fill(all(level),-1);
    level[u]=0;
    queue<int> q;q.push(u);
    while(!q.empty()){
        auto it=q.front();q.pop();
        for(auto &e:adj[it]){
            if(e.cost-e.flow>0 and level[e.to]==-1){
                level[e.to]=level[it]+1;
                q.push(e.to);
            }
        }
    }
    return !(level[v]==-1);
}
ll dfs(int v,int t,ll pushed){
    if(pushed==0 or v==t) return pushed;
    for(int &cid=ptr[v];cid<adj[v].size();cid++){
        auto &edge=adj[v][cid];
        int tr=edge.to;
        if(level[v]+1!=level[tr] or edge.cost-edge.flow==0) continue;
        ll push=dfs(tr,t,min(pushed,edge.cost-edge.flow));
        if(push==0) continue;;
        edge.flow+=push;
        adj[tr][edge.rev].flow-=push;
        return push;
    }
    return 0;
}
ll dinic(int s,int t){
    ll ans=0;
    while(bfs(s,t)){
        fill(all(ptr),0);
        while(ll push=dfs(s,t,infll)){
            ans+=push;
        }
    }
    return ans;
}
struct node1{
    double expi;
    int useda;int usedb;
};
const double eps=1e-9;
struct pt{
    int l,r,id;
    bool operator<(const pt&ot) const{
        return l<ot.l;
    }
};
struct cmp{
    bool operator()(const pt& a,const pt &b){
          return a.r>b.r;
    }
};
int dx[]={-1,1,0,0};
int dy[]={0,0,1,-1};
 
void solve(){
  ll n;cin>>n;
  if(n==1){
    cout<<1<<endl;
  }
  else if(n==2){
    cout<<-1<<endl;
  }
  else{
    vi ans={1,2,3};
    ll sum=6;
    while(ans.size()<n){
       ans.pb(sum);
       sum*=2;
    }
  L(i,0,n-1){
    cout<<ans[i]<<" ";
  }
  cout<<endl;
}
}
signed main(){
    ios_base::sync_with_stdio(0);
    cin.tie(0);
    int tc;cin>>tc;
    //memset(dp,-1,sizeof(dp));a
    //prestir();
   //int tc=1; 
   //spfi();
    //build_spf();
   // init();
    //spfa();
   // pre1();
   //precompute(mod);
    while(tc--){
        solve();
    }
    return 0;
}