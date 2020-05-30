/*
Articulation Points and Bridges =>

Given an undirected graph containing N vertices and M edges, find all the articulation points and all the bridges in the graph.

Input:
First line consists of two space separated integers denoting N and M. M lines follow, each containing two space separated integers X and Y denoting there is an edge between X and Y.

Output:
If the number of articulation points in the graph is p and that of bridges is q , then print as shown below:
p
p space separated integers, the articulation points, sorted in increasing order
q
q lines, each containing two space separated integers, the bridges in the graph. For a bridge u-v, print u first if u < v, otherwise print v first. Print all the bridges in increasing order of first vertex, and if first vertex is same, then in increasing order of second vertex.

Constraints:
1 ≤ N, M ≤ 10
0 ≤ X, Y ≤ N-1

*/


#include <bits/stdc++.h>
using namespace std;
#define f first
#define s second  
#define eb emplace_back
#define pb push_back
#define mp make_pair
#define pi acos(-1.0) //pi=3.14159...
#define nline printf("\n")
#define mem(arr,b) memset(arr,b,sizeof(arr))
#define popcount __builtin_popcountll
#define boost ios_base::sync_with_stdio(false);cin.tie(NULL);cout.tie(nullptr) //For FAST I/O 
 
//debugging snippets
#define debug(x)        cout<<__FUNCTION__<<":"<<__LINE__<<": "#x" = "<<x<<"\n";
#define debug2(x, y)     cout<<__FUNCTION__<<":"<<__LINE__<<": "#x" = "<<x<<" | "#y" = "<<y<<"\n";
#define debug3(x, y, z)  cout<<__FUNCTION__<<":"<<__LINE__<<": "#x" = "<<x<<" | "#y" = "<<y<<" | "#z" ="<<z<<"\n";
#define debug4(x, y, z ,w)  cerr<<__FUNCTION__<<":"<<__LINE__<<": "#x" = "<<x<<" | "#y" = "<<y<<" | "#z" ="<<z<<" | "#w" ="<<w<<"\n";
 
 
typedef long long ll;
typedef long double ld;
typedef unsigned int uint;
typedef unsigned long long ull;
typedef std::pair<int, int> pii;
typedef std::pair<char, char> pcc;
typedef std::pair<double, double> pdd;
typedef std::pair<std::string, std::string> pss;
typedef std::pair<long, long> pll;
typedef std::pair<ll, ll> pLL;
typedef std::vector<int> vint;
typedef std::vector<pii> vpii;
typedef std::vector<long> vlong;
typedef std::vector<long long> vll;
typedef std::vector<std::string> vstr;
typedef std::vector<bool> vbool;


#define all(X) (X).begin(), (X).end()
#define reunique(v) v.resize(std::unique(v.begin(), v.end()) - v.begin())
#define sort_unique(c) (sort(c.begin(), c.end()), c.resize(std::distance(c.begin(), std::unique(c.begin(),c.end()))))

#define sqr(_) ((_)*(_))
#define sqrt(__) sqrt(1.0*(__))
#define pow(_, __) pow(1.0*(_), __)

#define checkbit(n, b) (((n) >> (b)) & 1)
#define setbit(n, b) ((n) | (static_cast<std::decay<decltype(n)>::type>(1) << (b)))
#define removebit(n, b) ((n) & ~(static_cast<std::decay<decltype(n)>::type>(1) << (b)))
#define flipbit(n, b) ((n) ^ (static_cast<std::decay<decltype(n)>::type>(1)<<(b)))
inline int countBits(uint v){v=v-((v>>1)&0x55555555);v=(v&0x33333333)+((v>>2)&0x33333333);return((v+(v>>4)&0xF0F0F0F)*0x1010101)>>24;}
inline int countBits(ull v){uint t=v>>32;uint p=(v & ((1ULL << 32) - 1)); return countBits(t) + countBits(p); }
inline int countBits(ll v){return countBits((ull)v); }
inline int countBits(int v){return countBits((uint)v); }
unsigned int reverseBits(uint x){ x = (((x & 0xaaaaaaaa) >> 1) | ((x & 0x55555555) << 1)); x = (((x & 0xcccccccc) >> 2) | ((x & 0x33333333) << 2)); x = (((x & 0xf0f0f0f0) >> 4) | ((x & 0x0f0f0f0f) << 4)); x = (((x & 0xff00ff00) >> 8) | ((x & 0x00ff00ff) << 8)); return((x >> 16) | (x << 16)); }
inline bool isPowerOfTwo(int x){ return (x != 0 && (x&(x - 1)) == 0); }

//Pair magic *****************************************************************************************************
#define TT1T2 template<class T1, class T2>
#define PT1T2 pair<T1, T2>
TT1T2 inline PT1T2 operator+(const PT1T2 &p1 , const PT1T2 &p2) { return PT1T2(p1.first + p2.first, p1.second + p2.second); }
TT1T2 inline PT1T2& operator+=(PT1T2 &p1 , const PT1T2 &p2) { p1.first += p2.first, p1.second += p2.second; return p1; }
TT1T2 inline PT1T2 operator-(const PT1T2 &p1 , const PT1T2 &p2) { return PT1T2(p1.first - p2.first, p1.second - p2.second); }
TT1T2 inline PT1T2& operator-=(PT1T2 &p1 , const PT1T2 &p2) { p1.first -= p2.first, p1.second -= p2.second; return p1; }

template<class T> inline T _gcd(T a, T b) { while (b) { T t = a % b; a = b; b = t; } return a; }
template<class T> inline T _gcd(T a, T b, T c){ return _gcd(_gcd(a, b), c); }
template<class T>
T fast_gcd(T u, T v) {
    int shl = 0; while ( u && v && u != v) { T eu = u & 1; u >>= eu ^ 1; T ev = v & 1; v >>= ev ^ 1;
        shl += (~(eu | ev) & 1); T d = u & v & 1 ? (u + v) >> 1 : 0; T dif = (u - v) >> (sizeof(T) * 8 - 1); u -= d & ~dif; v -= d & dif;
    } return std::max(u, v) << shl;
}

ll gcdex(ll a, ll b, ll& x, ll& y) {
    if (!a) { x = 0; y = 1; return b; }
    ll y1; ll d = gcdex(b % a, a, y, y1); x = y1 - (b / a) * y;
    return d;
}
template<class T> bool isPrime(T x) { if (x <= 4 || x % 2 == 0 || x % 3 == 0) return x == 2 || x == 3;
    for (T i = 5; i * i <= x; i += 6) if (x % i == 0 || x % (i + 2) == 0) return 0; return 1; }

template<class T> inline void normmod(T &x, T m) { x %= m; if (x < 0) x += m; }
#if INTPTR_MAX == INT32_MAX or !defined(__SIZEOF_INT128__)
inline ll mulmod(ll x, ll n, ll m){ ll r = 0; normmod(x, m); normmod(n, m); while (n) { if (n & 1) r += x; x += x; if (r >= m) r -= m; if (x >= m) x -= m; n /= 2; } return r; }
#else
using int128 = __int128;
inline ll mulmod(ll x, ll n, ll m){ return __int128(x) * n % m; }
#endif
inline ll powmod(ll x, ll n, ll m){ ll r = 1; normmod(x, m); while (n){ if (n & 1) r *= x; x *= x; r %= m; x %= m; n /= 2; }return r; }
inline ll powmulmod(ll x, ll n, ll m) { ll res = 1; normmod(x, m); while (n){ if (n & 1)res = mulmod(res, x, m); x = mulmod(x, x, m); n /= 2; } return res; }
bool millerRabin(long long n) {
    if (n <= 1000) return isPrime(n);
    long long s = n - 1; int t = 0; while (s % 2 == 0) s /= 2, ++t;
    for (int a : {2, 325, 9375, 28178, 450775, 9780504, 1795265022}) { if (!(a %= n)) return true;
        long long f = powmulmod(a, s, n); if (f == 1 || f == n - 1) continue;
        for (int i = 1; i < t; ++i) if ((f = mulmod(f, f, n)) == n - 1) goto nextp;
        return false; nextp:;
    } return true;
}
                        
                        template<class T>
                        T mod(T a, T b) {
                            if (a<0){   
                                a=(-a)%b ;
                                if (a!=0){
                                   a=b-a ;
                                }
                            }else{
                                a=a%b ;
                            }
                            return a ;
                        }

                        template<class T>
                        T mul(T a, T b, T mm) {
                            return (mod(a, mm) * mod(b, mm))%mm ;
                        }
 
                        template<class T>
                        T add(T a, T b, T mm) {
                            return (mod(a, mm) + mod(b, mm))%mm ;
                        }
                        

                        template<class T>
                        T gcd (T a, T b){                       
                            if (a==-1||b==-1)return -1 ;
                            if (a==0||b==0)return b|a ;
                            return (std::__gcd(a,b)) ;
                        }
 
 
                        template<class T>
                        T lcm (T a, T b){
                            if(a==0 && b==0) return 0;
                            return (a*b)/(std::__gcd(a,b)) ;
                        }

           //Use fastscan(int) function to scan integer_inputs only. Don't Use fastscan() for character_inputs or Other than integers
                      
                        void fastscan(int &number){
                            bool negative = false;
                            register int c;
                            number = 0;
                            c = getchar();
                            if (c=='-')
                            {
                              negative = true;
                              c = getchar();
                            }
                            for (; (c>47 && c<58); c=getchar())
                            number = number *10 + c - 48;
                             if (negative)
                            number *= -1;
                        }

                        bool *is_prime;
                        void sieve(void){
                            const int MAX_N = 1e5 + 5;
                            is_prime = new bool[MAX_N];
                            memset(is_prime, true, MAX_N);
                         
                            for (int p=1<<1; p*p<=MAX_N; ++p){
                                if (is_prime[p]){
                                    for (int i=p<<1; i<=MAX_N; i += p)
                                        is_prime[i] = false;
                                }
                            }
                        }


                        int* ni(int n){                       
                            int *arr = new int[n];
                            for(int i=0; i<n; ++i){
                                cin>>arr[i];
                            }
                           return arr;  
                        }

                        long* nl(int n){                       
                            long *arr = new long[n];
                            for(int i=0; i<n; ++i){
                                cin>>arr[i];
                            }
                           return arr;  
                        }

                        long long* nll(int n){                       
                            long long *arr = new long long[n];
                            for(int i=0; i<n; ++i){
                                cin>>arr[i];
                            }
                           return arr;  
                        }
 
// int some_primes[7] = {24443, 100271, 1000003, 1000333, 5000321, 98765431, 1000000123};
#define alphabets "abcdefghijklmnopqrstuvwxyz"
#define ALPHABETS "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
// unordered_map<ll , ll> lol, freq;
// map<ll, ll> mp;
// set<int> s;
// multiset<int> ms;
// stack<int> stk;
// queue<int> q;
// dequeue<int> dq;

// class cmp{
// public:
//     bool operator()(T const& LHS, T const& RHS) const{
//         return (bool)(some_expression);
//     }
// };

// bool cmp(T const& a, T const& b){
//     return (bool)(some_expression);
// }

int32_t __(void);
int32_t main(int argc, char** argv){
    boost;
    clock_t clk;
    clk = clock();
    int32_t _ = __();
    clk = clock() - clk;
    //cerr <<"\n==> Execution Time: "  << ((double)clk)/CLOCKS_PER_SEC ;
    //printf("\n==> Execution Time: %lf", ((double)clk)/CLOCKS_PER_SEC);
return _;
}
                        // Write Your Code Here ... //
//Define Your Functions From Here...
const int N = 3e3+ 10;
const int inf = 1e9 + 5;
const ll MOD = 1e9 + 7;
vector<int> adj[N];
bool visited[N], isArticulation[N];
int visitedTime[N], lowTime[N];
vpii bridges;
vint articulationPoints;

void dfs_for_finding_articulation_points(int u, int par, int time){
    //debug2(u, time);
    visited[u] = true;
    visitedTime[u] = lowTime[u] = time;
    int childCount = 0;
    for(int v : adj[u]){
        if(v == par){
            continue;
        }
        if(!visited[v]){
            dfs_for_finding_articulation_points(v, u, time+1);
            lowTime[u] = min(lowTime[u], lowTime[v]);
            if(par == -1 and ++childCount>1){
                isArticulation[u] = true;
                articulationPoints.pb(u);
            }
            if(par != -1 and visitedTime[u] <= lowTime[v]){//Used sign "<=" for finding articulation-points
                isArticulation[u] = true;
                articulationPoints.pb(u);
            }
            if( visitedTime[u] < lowTime[v]){//Used sign "<" for finding bridges
                bridges.pb({min(u, v), max(u, v)});
            }
        }else{
            lowTime[u] = min(lowTime[u], visitedTime[v]);
        }
    }
}
int32_t __(void){
    int n, m;
    cin>>n>>m;
    while(m--){
        int u, v;
        cin>>u>>v;
        adj[u].pb(v);
        adj[v].pb(u);
    }
    mem(visited, false);
    mem(visitedTime, 0);
    mem(lowTime, 0);
    mem(isArticulation, false);
    bridges = vpii();
    for(int i=0; i<n; ++i){
        if(!visited[i]){
            dfs_for_finding_articulation_points(i, -1, 0);//(node, node's parent, startValue for time)
        }
    }
    cout<<articulationPoints.size()<<"\n";
    sort(all(articulationPoints));
    for(int articulationPoint : articulationPoints){
        cout<<articulationPoint<<" ";
    }
    if(!articulationPoints.empty()){
        cout<<"\n";
    }
    cout<<bridges.size()<<"\n";
    sort(all(bridges), [&] (pii const& a, pii const& b){
        return a.f != b.f ? a.f < b.f : a.s < b.s;
    });
    for(pii bridge : bridges){
        cout<<bridge.f<<" "<<bridge.s<<"\n";
    }
    return 0;
}
