/* NFSW GhostBird · NEED FOR SWEEP · NonStop VM Scanner (native) v1.1.0
 * Educational random scanner for unsolved Bitcoin Puzzle ranges. CPU only, no deps.
 * Build: gcc -O3 -march=native -pthread -o nfsw nfsw.c
 * Run:   ./nfsw targets.txt [threads] [watchdog_sec]   |  ./nfsw --selftest  |  ./nfsw --hash <privkey_hex>
 * targets.txt lines: puzzle#,address   (or puzzle#,hash160hex40)
 * Credits: multi-ai-agent · dra69on · aoxy · agnarez · 0xindy · 0xfinu · zync · claude.ai research (c) 2026 */
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <pthread.h>
#include <unistd.h>
#include <signal.h>
#include <time.h>
#include <sys/mman.h>
#include <sys/wait.h>
#include <sys/random.h>
#ifdef __linux__
#include <sys/prctl.h>
#endif
typedef uint64_t u64; typedef uint32_t u32; typedef uint8_t u8; typedef unsigned __int128 u128;
#define VER "1.1.0"
#define BATCH 1024
#define MAXT 256
/* ---------- field arithmetic mod p = 2^256 - 2^32 - 977 ---------- */
static const u64 CC=0x1000003D1ULL, P0=0xFFFFFFFEFFFFFC2FULL;
static inline int ge_p(const u64*a){return a[3]==~0ULL&&a[2]==~0ULL&&a[1]==~0ULL&&a[0]>=P0;}
static inline void add_c(u64*a){u128 x=(u128)a[0]+CC;a[0]=(u64)x;u64 c=x>>64;for(int i=1;i<4;i++){x=(u128)a[i]+c;a[i]=(u64)x;c=x>>64;}}
static inline void sub_c(u64*a){u128 x=(u128)a[0]-CC;a[0]=(u64)x;u64 b=(x>>64)&1;for(int i=1;i<4;i++){x=(u128)a[i]-b;a[i]=(u64)x;b=(x>>64)&1;}}
static inline void fe_add(u64*r,const u64*a,const u64*b){u128 x;u64 c=0;for(int i=0;i<4;i++){x=(u128)a[i]+b[i]+c;r[i]=(u64)x;c=x>>64;}if(c||ge_p(r))add_c(r);}
static inline void fe_sub(u64*r,const u64*a,const u64*b){u64 br=0;for(int i=0;i<4;i++){u128 x=(u128)a[i]-b[i]-br;r[i]=(u64)x;br=(x>>64)&1;}if(br)sub_c(r);}
static void fe_mul(u64*r,const u64*a,const u64*b){
  u64 t[8]={0};
  for(int i=0;i<4;i++){u64 c=0;for(int j=0;j<4;j++){u128 x=(u128)a[i]*b[j]+t[i+j]+c;t[i+j]=(u64)x;c=x>>64;}t[i+4]=c;}
  u64 s[5];u128 c=0;
  for(int i=0;i<4;i++){u128 x=(u128)t[4+i]*CC+t[i]+c;s[i]=(u64)x;c=x>>64;}
  s[4]=(u64)c;
  u128 x=(u128)s[4]*CC+s[0];r[0]=(u64)x;c=x>>64;
  for(int i=1;i<4;i++){x=(u128)s[i]+c;r[i]=(u64)x;c=x>>64;}
  if(c)add_c(r);
  if(ge_p(r))add_c(r);
}
static void fe_inv(u64*r,const u64*a){
  static const u64 E[4]={0xFFFFFFFEFFFFFC2DULL,~0ULL,~0ULL,~0ULL};
  u64 res[4]={1,0,0,0},b[4];memcpy(b,a,32);
  for(int i=0;i<256;i++){if((E[i>>6]>>(i&63))&1)fe_mul(res,res,b);fe_mul(b,b,b);}
  memcpy(r,res,32);
}
/* ---------- curve (Jacobian) ---------- */
static const u64 GX[4]={0x59F2815B16F81798ULL,0x029BFCDB2DCE28D9ULL,0x55A06295CE870B07ULL,0x79BE667EF9DCBBACULL};
static const u64 GY[4]={0x9C47D08FFB10D4B8ULL,0xFD17B448A6855419ULL,0x5DA4FBFC0E1108A8ULL,0x483ADA7726A3C465ULL};
typedef struct{u64 x[4],y[4],z[4];}pt;
#define M(r,a,b) fe_mul(r,a,b)
static void pdbl(pt*p){
  u64 A[4],B[4],C[4],D[4],E[4],F[4],t[4];
  M(A,p->x,p->x);M(B,p->y,p->y);M(C,B,B);
  fe_add(t,p->x,B);M(t,t,t);fe_sub(t,t,A);fe_sub(t,t,C);fe_add(D,t,t);
  fe_add(E,A,A);fe_add(E,E,A);M(F,E,E);
  u64 X3[4],Y3[4],Z3[4];fe_add(t,D,D);fe_sub(X3,F,t);
  fe_sub(t,D,X3);M(Y3,E,t);fe_add(C,C,C);fe_add(C,C,C);fe_add(C,C,C);fe_sub(Y3,Y3,C);
  M(Z3,p->y,p->z);fe_add(Z3,Z3,Z3);
  memcpy(p->x,X3,32);memcpy(p->y,Y3,32);memcpy(p->z,Z3,32);
}
static void padd_g(pt*p){ /* p += G (mixed) */
  u64 ZZ[4],H[4],HH[4],I[4],J[4],r[4],V[4],t[4],X3[4],Y3[4],Z3[4];
  M(ZZ,p->z,p->z);M(t,GX,ZZ);fe_sub(H,t,p->x);M(HH,H,H);
  fe_add(I,HH,HH);fe_add(I,I,I);M(J,H,I);
  M(t,GY,p->z);M(t,t,ZZ);fe_sub(t,t,p->y);fe_add(r,t,t);
  M(V,p->x,I);
  M(X3,r,r);fe_sub(X3,X3,J);fe_sub(X3,X3,V);fe_sub(X3,X3,V);
  fe_sub(t,V,X3);M(Y3,r,t);M(t,p->y,J);fe_add(t,t,t);fe_sub(Y3,Y3,t);
  fe_add(t,p->z,H);M(Z3,t,t);fe_sub(Z3,Z3,ZZ);fe_sub(Z3,Z3,HH);
  memcpy(p->x,X3,32);memcpy(p->y,Y3,32);memcpy(p->z,Z3,32);
}
static void pmul(pt*r,const u64*k){
  int top=255;while(top>=0&&!((k[top>>6]>>(top&63))&1))top--;
  memcpy(r->x,GX,32);memcpy(r->y,GY,32);r->z[0]=1;r->z[1]=r->z[2]=r->z[3]=0;
  for(int i=top-1;i>=0;i--){pdbl(r);if((k[i>>6]>>(i&63))&1)padd_g(r);}
}
/* ---------- SHA256 / RIPEMD160 ---------- */
static const u32 KS[64]={0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2};
static const u32 SIV[8]={0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19};
#define ROR(x,n) (((x)>>(n))|((x)<<(32-(n))))
#define ROL(x,n) (((x)<<(n))|((x)>>(32-(n))))
static void sha_c(u32*h,const u8*b){
  u32 w[64];for(int i=0;i<16;i++)w[i]=__builtin_bswap32(((const u32*)b)[i]);
  for(int i=16;i<64;i++){u32 a=w[i-15],c=w[i-2];w[i]=w[i-16]+(ROR(a,7)^ROR(a,18)^(a>>3))+w[i-7]+(ROR(c,17)^ROR(c,19)^(c>>10));}
  u32 a=h[0],bb=h[1],c=h[2],d=h[3],e=h[4],f=h[5],g=h[6],hh=h[7];
  for(int i=0;i<64;i++){u32 t1=hh+(ROR(e,6)^ROR(e,11)^ROR(e,25))+((e&f)^(~e&g))+KS[i]+w[i],t2=(ROR(a,2)^ROR(a,13)^ROR(a,22))+((a&bb)^(a&c)^(bb&c));hh=g;g=f;f=e;e=d+t1;d=c;c=bb;bb=a;a=t1+t2;}
  h[0]+=a;h[1]+=bb;h[2]+=c;h[3]+=d;h[4]+=e;h[5]+=f;h[6]+=g;h[7]+=hh;
}
static void sha256(const u8*m,size_t n,u8*out){
  u32 h[8];memcpy(h,SIV,32);u8 blk[128]={0};size_t i=0;
  for(;i+64<=n;i+=64)sha_c(h,m+i);
  size_t r=n-i;memcpy(blk,m+i,r);blk[r]=0x80;size_t L=(r<56)?64:128;
  u64 bits=(u64)n*8;for(int j=0;j<8;j++)blk[L-1-j]=bits>>(8*j);
  sha_c(h,blk);if(L==128)sha_c(h,blk+64);
  for(int j=0;j<8;j++){u32 v=__builtin_bswap32(h[j]);memcpy(out+4*j,&v,4);}
}
static const u8 RL[80]={0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,7,4,13,1,10,6,15,3,12,0,9,5,2,14,11,8,3,10,14,4,9,15,8,1,2,7,0,6,13,11,5,12,1,9,11,10,0,8,12,4,13,3,7,15,14,5,6,2,4,0,5,9,7,12,2,10,14,1,3,8,11,6,15,13};
static const u8 RR[80]={5,14,7,0,9,2,11,4,13,6,15,8,1,10,3,12,6,11,3,7,0,13,5,10,14,15,8,12,4,9,1,2,15,5,1,3,7,14,6,9,11,8,12,2,10,0,4,13,8,6,4,1,3,11,15,0,5,12,2,13,9,7,10,14,12,15,10,4,1,5,8,7,6,2,13,14,0,3,9,11};
static const u8 SL[80]={11,14,15,12,5,8,7,9,11,13,14,15,6,7,9,8,7,6,8,13,11,9,7,15,7,12,15,9,11,7,13,12,11,13,6,7,14,9,13,15,14,8,13,6,5,12,7,5,11,12,14,15,14,15,9,8,9,14,5,6,8,6,5,12,9,15,5,11,6,8,13,12,5,12,13,14,11,8,5,6};
static const u8 SR[80]={8,9,9,11,13,15,15,5,7,7,8,11,14,14,12,6,9,13,15,7,12,8,9,11,7,7,12,7,6,15,13,11,9,7,15,11,8,6,6,14,12,13,5,14,13,13,7,5,15,5,8,11,14,14,6,14,6,9,12,9,12,5,15,8,8,5,12,9,12,5,14,6,8,13,6,5,15,13,11,11};
static const u32 KL[5]={0,0x5A827999,0x6ED9EBA1,0x8F1BBCDC,0xA953FD4E},KR[5]={0x50A28BE6,0x5C4DD124,0x6D703EF3,0x7A6D76E9,0};
static inline u32 F5(int q,u32 x,u32 y,u32 z){switch(q){case 0:return x^y^z;case 1:return(x&y)|(~x&z);case 2:return(x|~y)^z;case 3:return(x&z)|(y&~z);default:return x^(y|~z);}}
static void rmd_blk(const u32*X,u32*o){ /* single block, standard IV, output 5 LE words */
  u32 a=0x67452301,b=0xefcdab89,c=0x98badcfe,d=0x10325476,e=0xc3d2e1f0,A=a,B=b,C=c,D=d,E=e,T;
  for(int j=0;j<80;j++){int q=j>>4;
    T=ROL(a+F5(q,b,c,d)+X[RL[j]]+KL[q],SL[j])+e;a=e;e=d;d=ROL(c,10);c=b;b=T;
    T=ROL(A+F5(4-q,B,C,D)+X[RR[j]]+KR[q],SR[j])+E;A=E;E=D;D=ROL(C,10);C=B;B=T;}
  T=0xefcdab89u + c + D;o[1]=0x98badcfeu + d + E;o[2]=0x10325476u + e + A;o[3]=0xc3d2e1f0u + a + B;o[4]=0x67452301u + b + C;o[0]=T;
}
static inline void h160(const u64*x,int odd,u32*out){
  u8 blk[64]={0};blk[0]=2|odd;
  for(int i=0;i<4;i++){u64 w=x[3-i];for(int j=0;j<8;j++)blk[1+8*i+j]=(u8)(w>>(56-8*j));}
  blk[33]=0x80;blk[62]=1;blk[63]=8;
  u32 h[8];memcpy(h,SIV,32);sha_c(h,blk);
  u32 X[16]={0};for(int i=0;i<8;i++)X[i]=__builtin_bswap32(h[i]);X[8]=0x80;X[14]=256;
  rmd_blk(X,out);
}
/* ---------- batch: hashes of (k+i)*G, i<BATCH ---------- */
static void batch_hash(const u64*k,u32 (*out)[5]){
  static __thread pt pts[BATCH];static __thread u64 acc[BATCH][4];
  pt p;pmul(&p,k);
  for(int i=0;i<BATCH;i++){pts[i]=p;if(i)M(acc[i],acc[i-1],p.z);else memcpy(acc[0],p.z,32);if(i<BATCH-1)padd_g(&p);}
  u64 iv[4];fe_inv(iv,acc[BATCH-1]);
  for(int i=BATCH-1;i>=0;i--){
    u64 zi[4],z2[4],x[4],y[4];
    if(i)M(zi,iv,acc[i-1]);else memcpy(zi,iv,32);
    M(iv,iv,pts[i].z);
    M(z2,zi,zi);M(x,pts[i].x,z2);M(y,pts[i].y,z2);M(y,y,zi);
    h160(x,(int)(y[0]&1),out[i]);
  }
}
/* ---------- targets ---------- */
typedef struct{int n;u8 h[20];char a[48];}tgt;
static tgt T[512];static int NT=0;static short TB[4096];
static const char*A58="123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
static int dec58(const char*s,u8*h160){
  u8 b[25]={0};for(const char*p=s;*p;p++){const char*q=strchr(A58,*p);if(!q||!*p)return 0;unsigned c=q-A58;
    for(int j=24;j>=0;j--){c+=58*b[j];b[j]=c&255;c>>=8;}if(c)return 0;}
  u8 d1[32],d2[32];sha256(b,21,d1);sha256(d1,32,d2);if(memcmp(d2,b+21,4)||b[0]!=0)return 0;
  memcpy(h160,b+1,20);return 1;
}
static int load(const char*f){
  FILE*fp=fopen(f,"r");if(!fp){perror(f);return 0;}char ln[256];
  while(fgets(ln,sizeof ln,fp)&&NT<512){int n;char a[128];
    if(sscanf(ln," %d%*[,; \t]%127s",&n,a)!=2||n<20||n>160)continue;
    tgt*t=&T[NT];t->n=n;int ok=0;
    if(strlen(a)==40){ok=1;for(int i=0;i<20;i++){unsigned v;if(sscanf(a+2*i,"%2x",&v)!=1){ok=0;break;}t->h[i]=v;}}
    else ok=dec58(a,t->h);
    if(!ok){fprintf(stderr,"skip (invalid/checksum): %s",ln);continue;}
    strncpy(t->a,a,47);NT++;}
  fclose(fp);
  memset(TB,0,sizeof TB);
  for(int i=0;i<NT;i++){u32 w;memcpy(&w,T[i].h,4);unsigned s=w&4095;while(TB[s])s=(s+1)&4095;TB[s]=i+1;}
  return NT;
}
/* ---------- shared state / threads ---------- */
typedef struct{volatile u64 cnt[MAXT],beat[MAXT];volatile u64 restarts;}shm_t;
static shm_t*S;static int NTH=1;
static u64 now_ms(void){struct timespec ts;clock_gettime(CLOCK_MONOTONIC,&ts);return ts.tv_sec*1000ULL+ts.tv_nsec/1000000;}
static void rnd(void*b,size_t n){size_t o=0;while(o<n){ssize_t r=getrandom((u8*)b+o,n-o,0);if(r>0)o+=r;}}
static void hexs(const u64*k,char*o){sprintf(o,"%016llx%016llx%016llx%016llx",(unsigned long long)k[3],(unsigned long long)k[2],(unsigned long long)k[1],(unsigned long long)k[0]);}
static void* worker(void*arg){
  int id=(int)(long)arg;u32 (*out)[5]=malloc(sizeof(u32)*5*BATCH);
  while(1){
    u64 r[5];rnd(r,sizeof r);const tgt*t=&T[r[4]%NT];int n=t->n;
    u64 k[4]={r[0],r[1],r[2],r[3]};
    for(int i=0;i<4;i++){int lo=i*64;if(n-1<=lo)k[i]=0;else if(n-1<lo+64)k[i]&=((1ULL<<(n-1-lo))-1);}
    k[(n-1)>>6]|=1ULL<<((n-1)&63);                       /* force range [2^(n-1), 2^n) */
    u64 k2[4]={k[0]+BATCH,k[1],k[2],k[3]};if(k2[0]<k[0]){if(!++k2[1])if(!++k2[2])++k2[3];}
    if((k2[(n)>>6]>>(n&63))&1){u64 b=k[0];k[0]-=BATCH;if(k[0]>b){if(!k[1]--){if(!k[2]--)k[3]--;}}}
    batch_hash(k,out);
    for(int i=0;i<BATCH;i++){
      for(unsigned s=out[i][0]&4095;TB[s];s=(s+1)&4095){const tgt*m=&T[TB[s]-1];
        if(!memcmp(m->h,out[i],20)){u64 kk[4]={k[0]+i,k[1],k[2],k[3]};if(kk[0]<k[0]){if(!++kk[1])if(!++kk[2])++kk[3];}
          char hx[80];hexs(kk,hx);
          FILE*f=fopen("found.txt","a");if(f){fprintf(f,"PUZZLE %d %s PRIVKEY %s\n",m->n,m->a,hx);fflush(f);fsync(fileno(f));fclose(f);}
          printf("\n*** FOUND *** puzzle %d %s privkey %s\n",m->n,m->a,hx);fflush(stdout);}}
    }
    S->cnt[id]+=BATCH;S->beat[id]=now_ms();
  }
  return 0;
}
static void run_child(void){
#ifdef __linux__
  prctl(PR_SET_PDEATHSIG,SIGKILL);
#endif
  pthread_t th;u64 t=now_ms();for(int i=0;i<NTH;i++)S->beat[i]=t;
  for(int i=0;i<NTH;i++)pthread_create(&th,0,worker,(void*)(long)i);
  while(1)pause();
}
static pid_t child=0;static void onint(int s){(void)s;if(child)kill(child,SIGKILL);printf("\nstopped\n");_exit(0);}
/* ---------- selftest ---------- */
static void hx20(const u32*o,char*s){const u8*b=(const u8*)o;for(int i=0;i<20;i++)sprintf(s+2*i,"%02x",b[i]);}
static int selftest(void){
  int ok=1;char s[48];u32 o[5];
  u64 a[4]={0x123456789abcdefULL,0xfedcba987654321ULL,5,7},b[4],c[4];fe_inv(b,a);fe_mul(c,a,b);
  int fe=(c[0]==1&&!c[1]&&!c[2]&&!c[3]);printf("field inverse: %s\n",fe?"PASS":"FAIL");ok&=fe;
  u64 one[4]={1,0,0,0};pt p;pmul(&p,one);u64 zi[4],z2[4],x[4],y[4];fe_inv(zi,p.z);M(z2,zi,zi);M(x,p.x,z2);M(y,p.y,z2);M(y,y,zi);
  h160(x,y[0]&1,o);hx20(o,s);int k1=!strcmp(s,"751e76e8199196d454941c45d1b3a323f1433bd6");printf("key=1 hash160 %s: %s\n",s,k1?"PASS":"FAIL");ok&=k1;
  u32 (*out)[5]=malloc(sizeof(u32)*5*BATCH);u64 k[4];rnd(k,8);k[0]=(k[0]&((1ULL<<60)-1))|(1ULL<<59);k[1]=k[2]=k[3]=0;
  batch_hash(k,out);int idx[4]={0,1,500,BATCH-1},bo=1;
  for(int j=0;j<4;j++){u64 kk[4]={k[0]+idx[j],0,0,0};pt q;pmul(&q,kk);fe_inv(zi,q.z);M(z2,zi,zi);M(x,q.x,z2);M(y,q.y,z2);M(y,y,zi);h160(x,y[0]&1,o);if(memcmp(o,out[idx[j]],20))bo=0;}
  printf("batch vs scalar-mul: %s\n",bo?"PASS":"FAIL");ok&=bo;
  u8 d[32];sha256((const u8*)"abc",3,d);int sh=(d[0]==0xba&&d[1]==0x78&&d[31]==0xad);printf("sha256(abc): %s\n",sh?"PASS":"FAIL");ok&=sh;
  printf("SELFTEST %s\n",ok?"PASS":"FAIL");return ok;
}
int main(int ac,char**av){
  if(ac>1&&!strcmp(av[1],"--selftest"))return !selftest();
  if(ac>2&&!strcmp(av[1],"--hash")){u64 k[4]={0};const char*h=av[2];size_t L=strlen(h);for(size_t i=0;i<L;i++){unsigned v;sscanf((char[]){h[i],0},"%x",&v);for(int j=3;j>0;j--)k[j]=(k[j]<<4)|(k[j-1]>>60);k[0]=(k[0]<<4)|v;}
    pt p;pmul(&p,k);u64 zi[4],z2[4],x[4],y[4];fe_inv(zi,p.z);M(z2,zi,zi);M(x,p.x,z2);M(y,p.y,z2);M(y,y,zi);u32 o[5];char s[48];h160(x,y[0]&1,o);hx20(o,s);puts(s);return 0;}
  if(ac<2){fprintf(stderr,"NFSW NonStop VM Scanner v" VER "\nusage: %s targets.txt [threads] [watchdog_sec] | --selftest | --hash <privhex>\n",av[0]);return 1;}
  if(!selftest()){fprintf(stderr,"refusing to run: selftest failed\n");return 2;}
  if(!load(av[1])){fprintf(stderr,"no valid targets\n");return 1;}
  NTH=ac>2?atoi(av[2]):(int)sysconf(_SC_NPROCESSORS_ONLN);if(NTH<1)NTH=1;if(NTH>MAXT)NTH=MAXT;
  int wd=ac>3?atoi(av[3]):10;if(wd<3)wd=3;
  S=mmap(0,sizeof(shm_t),PROT_READ|PROT_WRITE,MAP_SHARED|MAP_ANONYMOUS,-1,0);
  signal(SIGINT,onint);signal(SIGTERM,onint);
  printf("NFSW NonStop VM Scanner v" VER " | %d targets | %d VM modules | watchdog %ds | found.txt on hit\n",NT,NTH,wd);
  u64 t0=now_ms(),lastc=0,lastt=t0;
  while(1){
    if(!child){child=fork();if(child==0){run_child();_exit(0);}if(child<0){perror("fork");return 1;}}
    sleep(1);
    int st;pid_t w=waitpid(child,&st,WNOHANG);int dead=(w==child);u64 n=now_ms();
    for(int i=0;i<NTH&&!dead;i++)if(n-S->beat[i]>(u64)wd*1000){fprintf(stderr,"\nwatchdog: VM%d stalled -> restarting\n",i);kill(child,SIGKILL);waitpid(child,&st,0);dead=1;}
    if(dead){if(w==child)fprintf(stderr,"\nwatchdog: child died -> restarting\n");child=0;S->restarts++;continue;}
    u64 tot=0;for(int i=0;i<NTH;i++)tot+=S->cnt[i];
    double sp=(tot-lastc)*1000.0/(double)(n-lastt+1);lastc=tot;lastt=n;
    printf("\r%.0fs | %.2f Mkeys/s | total %.3e | restarts %llu   ",(n-t0)/1000.0,sp/1e6,(double)tot,(unsigned long long)S->restarts);fflush(stdout);
  }
}
