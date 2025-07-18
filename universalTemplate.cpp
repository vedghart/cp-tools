#include <bits/stdc++.h>
using namespace std;

/* ===================== FAST I/O ===================== */
#define fast_io ios::sync_with_stdio(false); cin.tie(nullptr);

/* ===================== SHORTCUTS ===================== */
#define int long long                  // Use long long by default
#define pb push_back
#define all(x) (x).begin(), (x).end()
#define rall(x) (x).rbegin(), (x).rend()
#define sz(x) (int)(x).size()
#define ff first
#define ss second
typedef vector<int> vi;
typedef pair<int,int> pii;
typedef vector<pii> vpii;

/* ===================== CONSTANTS ===================== */
const int INF = 1e18;
const int MOD = 1e9+7;                 // Common mod

/* ===================== DEBUG (works only locally) ===================== */
#ifndef ONLINE_JUDGE
    #define debug(x) cerr << #x << " = "; _print(x); cerr << endl;
#else
    #define debug(x)
#endif

// Debug print helpers
void _print(int x){cerr<<x;} void _print(string x){cerr<<x;}
void _print(char x){cerr<<x;} void _print(long double x){cerr<<x;}
template<class T,class V> void _print(pair<T,V> p){cerr<<"{";_print(p.ff);cerr<<",";_print(p.ss);cerr<<"}";}
template<class T> void _print(vector<T> v){cerr<<"[";for(auto i:v){_print(i);cerr<<" ";}cerr<<"]";}
template<class T> void _print(set<T> v){cerr<<"[";for(auto i:v){_print(i);cerr<<" ";}cerr<<"]";}
template<class T> void _print(multiset<T> v){cerr<<"[";for(auto i:v){_print(i);cerr<<" ";}cerr<<"]";}
template<class T,class V> void _print(map<T,V> v){cerr<<"[";for(auto i:v){_print(i.ff);cerr<<":";_print(i.ss);cerr<<" ";}cerr<<"]";}

/* ===================== MATH UTILITIES ===================== */
int mod_add(int a,int b,int m=MOD){return (a%m+b%m+m)%m;}
int mod_sub(int a,int b,int m=MOD){return (a%m-b%m+m)%m;}
int mod_mul(int a,int b,int m=MOD){return ((a%m)*(b%m))%m;}
int mod_pow(int a,int b,int m=MOD){
    int res=1; a%=m;
    while(b>0){
        if(b&1) res=(res*a)%m;
        a=(a*a)%m; b>>=1;
    }
    return res;
}
int mod_inv(int a,int m=MOD){return mod_pow(a,m-2,m);} // Fermat's theorem

/* ===================== COMBINATORICS (nCr) ===================== */
const int N = 1e6;
vi fact(N+1), invfact(N+1);

void precompute_factorials(){
    fact[0]=1;
    for(int i=1;i<=N;i++) fact[i]=mod_mul(fact[i-1],i);
    invfact[N]=mod_inv(fact[N]);
    for(int i=N-1;i>=0;i--) invfact[i]=mod_mul(invfact[i+1],i+1);
}
int nCr(int n,int r){
    if(r<0||r>n) return 0;
    return mod_mul(fact[n],mod_mul(invfact[r],invfact[n-r]));
}

/* ===================== DISJOINT SET (Union-Find) ===================== */
struct DSU {
    vi parent, size;
    DSU(int n){parent.resize(n); size.assign(n,1); iota(all(parent),0);}
    int find(int v){return v==parent[v]?v:parent[v]=find(parent[v]);}
    void unite(int a,int b){
        a=find(a); b=find(b);
        if(a!=b){
            if(size[a]<size[b]) swap(a,b);
            parent[b]=a; size[a]+=size[b];
        }
    }
};

/* ===================== FENWICK TREE (BIT) ===================== */
struct Fenwick {
    int n; vi bit;
    Fenwick(int n):n(n){bit.assign(n+1,0);}
    void update(int i,int val){for(;i<=n;i+=i&-i)bit[i]+=val;}
    int sum(int i){int s=0;for(;i>0;i-=i&-i)s+=bit[i];return s;}
    int range_sum(int l,int r){return sum(r)-sum(l-1);}
};

/* ===================== SEGMENT TREE ===================== */
struct SegmentTree {
    int n; vi tree;
    SegmentTree(int n):n(n){tree.assign(4*n,0);}
    void build(vi &a,int idx,int l,int r){
        if(l==r){tree[idx]=a[l];return;}
        int mid=(l+r)/2;
        build(a,2*idx,l,mid); build(a,2*idx+1,mid+1,r);
        tree[idx]=tree[2*idx]+tree[2*idx+1];
    }
    void update(int idx,int l,int r,int pos,int val){
        if(l==r){tree[idx]=val;return;}
        int mid=(l+r)/2;
        if(pos<=mid) update(2*idx,l,mid,pos,val);
        else update(2*idx+1,mid+1,r,pos,val);
        tree[idx]=tree[2*idx]+tree[2*idx+1];
    }
    int query(int idx,int l,int r,int ql,int qr){
        if(ql>r||qr<l) return 0;
        if(ql<=l&&r<=qr) return tree[idx];
        int mid=(l+r)/2;
        return query(2*idx,l,mid,ql,qr)+query(2*idx+1,mid+1,r,ql,qr);
    }
};

/* ===================== DIJKSTRA (Shortest Path) ===================== */
vector<int> dijkstra(int n, vector<vector<pii>>&adj, int src){
    vi dist(n,INF); dist[src]=0;
    priority_queue<pii, vector<pii>, greater<pii>> pq;
    pq.push({0,src});
    while(!pq.empty()){
        auto [d,u]=pq.top(); pq.pop();
        if(d!=dist[u]) continue;
        for(auto [v,w]:adj[u]){
            if(dist[u]+w<dist[v]){
                dist[v]=dist[u]+w;
                pq.push({dist[v],v});
            }
        }
    }
    return dist;
}

/* ===================== STRING ALGORITHMS ===================== */
// KMP Prefix Function
vi prefix_function(string s){
    int n=sz(s); vi pi(n,0);
    for(int i=1;i<n;i++){
        int j=pi[i-1];
        while(j>0 && s[i]!=s[j]) j=pi[j-1];
        if(s[i]==s[j]) j++;
        pi[i]=j;
    }
    return pi;
}
// Z-Algorithm
vi z_function(string s){
    int n=sz(s); vi z(n); z[0]=n;
    for(int i=1,l=0,r=0;i<n;i++){
        if(i<=r) z[i]=min(r-i+1,z[i-l]);
        while(i+z[i]<n && s[z[i]]==s[i+z[i]]) z[i]++;
        if(i+z[i]-1>r) l=i,r=i+z[i]-1;
    }
    return z;
}

/* ===================== SOLVE FUNCTION ===================== */
// Write problem logic here
void solve(){
    int x;
    cin>>x;
    string s=to_string(x);
    char ans='9';
    for(char c:s) ans=min(ans,c);
    cout<<(ans-'0')<<"\n";
}

/* ===================== MAIN ===================== */
int32_t main(){
    fast_io;
    // precompute_factorials(); // Uncomment if nCr is needed
    int t=1;
    cin>>t;
    while(t--) solve();
    return 0;
}
