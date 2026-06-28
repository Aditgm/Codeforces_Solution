#include<bits/stdc++.h>
//#include<ext/pb_ds/assoc_container.hpp>
using namespace std;
//using namespace __gnu_pbds;
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
const ll mod=1e9+7;
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
/*ll fact[N],inv[N];
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
*/
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
    Dsu(ll n=0):n(n),par(n+1),sz(n+1,1){iota(all(par),0);}
    ll find(ll x){
        return par[x]=(par[x]==x?x:find(par[x]));
    }
    bool unite(ll a,ll b){
        a=find(a),b=find(b);
        if(a==b) return 0;
        if(sz[a]<sz[b]) swap(a,b);
        par[b]=a;sz[a]+=sz[b];
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
const int phi=1e9+6;
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
const int n1=6e6+10;
int trie[n1][2];
int sz=1;
void insert(int val,int maxi){
    int cur=0;
    for(int i=maxi;i>=0;i--){
        int b=(val>>i)&1;
        if(!trie[cur][b]){
            trie[cur][b]=sz;
            trie[sz][0]=trie[sz][1]=0;
            sz++;
        }
        cur=trie[cur][b];
    }
}
int qry(int val,int maxi){
    int cur=0;
    int ans=0;
    for(int i=maxi;i>=0;i--){
        int b=(val>>i)&1;
        if(trie[cur][b]){
            cur=trie[cur][b];
        }
        else{
            cur=trie[cur][b^1]; //oppo lenge as it is option only.
            ans|=(1ll<<i);
        }
    }
    return ans;
}
ll rec(int l,int r,int bit,const vi &a){
    if(bit<0 or l>=r) return 0;
    int mid=l;
    while(mid<=r and ((a[mid]>>bit)&1)==0){
        mid++;
    }
    if(mid==l or mid>r){
        return rec(l,r,bit-1,a);
    }
    trie[0][0]=trie[0][1]=0;
    sz=1;
    L(i,l,mid-1){
        insert(a[i],bit-1);
    }
    int mini=inf;
    L(i,mid,r){
        mini=min(mini,qry(a[i],bit-1));
    }
    return (1ll<<bit)+mini+rec(l,mid-1,bit-1,a)+rec(mid,r,bit-1,a);
}
 
void solve(){
    int n,m;cin>>n>>m;
    Dsu ds(n);
    L(i,1,n){
        maxnode[i]=i;
    }
    L(i,0,m-1){
        int u,v;cin>>u>>v;
        ds.unite1(u,v);
    }
    int ans=0;
    int maxi=0;
    L(i,1,n){
        if(i<maxi){
            if(ds.find(i)!=ds.find(i-1)){
                ds.unite1(i,i-1);
                ans++;
            }
        }
        maxi=max(maxi,maxnode[ds.find(i)]);
    }
    cout<<ans<<endl;
}
 
signed main(){
    ios_base::sync_with_stdio(0);
    cin.tie(0);
   // int tc;cin>>tc;
    //memset(dp,-1,sizeof(dp));a
    //prestir();
   int tc=1; 
   //spfi();
    //build_spf();
   // init();
    //spfa();
    //pre();
   //precompute(mod);
    while(tc--){
        solve();
    }
    return 0;
}