// Exact interval arithmetic and finite NNS path regression. No dependencies.
// Source residual: SIGNED_MOBIUS_SPLIT_COMPENSATION_20261127.md; eta bracket as reported there.
// Finite tests, not an asymptotic sign proof.
function gcd(a,b){a=a<0n?-a:a;b=b<0n?-b:b;while(b){let t=a%b;a=b;b=t;}return a||1n;}
function Q(a,b=1n){a=BigInt(a);b=BigInt(b);if(b===0n)throw Error("zero denominator");if(b<0n){a=-a;b=-b;}let g=gcd(a,b);return [a/g,b/g];}
function add(a,b){return Q(a[0]*b[1]+b[0]*a[1],a[1]*b[1]);}
function neg(a){return [-a[0],a[1]];}
function sub(a,b){return add(a,neg(b));}
function mul(a,b){return Q(a[0]*b[0],a[1]*b[1]);}
function div(a,b){return Q(a[0]*b[1],a[1]*b[0]);}
function cmp(a,b){let d=a[0]*b[1]-b[0]*a[1];return d<0n?-1:d>0n?1:0;}
function fl(a){let q=a[0]/a[1];return a[0]<0n&&a[0]%a[1]!==0n?q-1n:q;}
function ce(a){return -fl(neg(a));}
function absQ(a){return a[0]<0n?neg(a):a;}
function isPrime(n){if(n<2)return false;for(let p=2;p*p<=n;p++)if(n%p===0)return false;return true;}
function nextPrime(n){let q=n+1;while(!isPrime(q))q++;return q;}
function mobius(n){let s=1;for(let p=2;p*p<=n;p++)if(n%p===0){n/=p;s=-s;if(n%p===0)return 0;}if(n>1)s=-s;return s;}
function U(t){if(cmp(t,Q(1))>0)return Q(0);let v=Q(0),rmax=Number(fl(div(Q(1),t)));for(let j=1;j<=rmax;j++){let mu=mobius(j);if(mu)v=add(v,mul(Q(mu),sub(div(Q(1),mul(Q(j),t)),Q(1))));}return v;}
function A(t){if(cmp(t,Q(1))>0||cmp(t,Q(0))<0)return Q(0);if(cmp(t,Q(1,2))>=0)return sub(div(Q(1),t),Q(1));return sub(Q(2),A(sub(Q(1),t)));}
function B(t){if(cmp(t,Q(1))>0||cmp(t,Q(0))<0)return Q(0);if(cmp(t,Q(1,2))<0)return neg(B(sub(Q(1),t)));return sub(U(mul(t,Q(1,2))),A(mul(t,Q(1,2))));}
function C0(t){if(cmp(t,Q(1))>0||cmp(t,Q(0))<0)return Q(0);if(cmp(t,Q(1,2))<0)return neg(C0(sub(Q(1),t)));if(cmp(t,Q(2,3))<=0)return Q(0);return sub(sub(U(mul(t,Q(1,4))),A(mul(t,Q(1,4)))),B(mul(t,Q(1,2))));}
function D(t){if(cmp(t,Q(1))>0||cmp(t,Q(0))<0)return Q(0);if(cmp(t,Q(1,2))<0)return neg(D(sub(Q(1),t)));let z=sub(Q(1),absQ(sub(mul(Q(12),t),Q(7))));return cmp(z,Q(0))>0?z:Q(0);}
function residual(n,m){let y=Q(n,m),a=Q(0),b=Q(0);for(let r=1;r*n<=m;r++){let t=mul(Q(r),y);a=add(a,add(A(t),add(B(mul(Q(2),t)),C0(mul(Q(4),t)))));b=add(b,D(mul(Q(4),t)));}return [sub(a,sub(div(Q(1),y),Q(1))),b];}
function rangeQ(xs){let a=xs[0],b=xs[0];for(const x of xs){if(cmp(x,a)<0)a=x;if(cmp(x,b)>0)b=x;}return [a,b];}
function logUnit(a){let z=div(sub(a,Q(1)),add(a,Q(1))),z2=mul(z,z),p=z,L=Q(0),J=20;for(let j=0;j<J;j++){L=add(L,mul(Q(2,2*j+1),p));p=mul(p,z2);}let tail=div(mul(Q(2,2*J+1),p),sub(Q(1),z2));return [L,add(L,tail)];}
function logBounds(p){let n=1,e=0;while(n*2<=p){n*=2;e++;}let a=logUnit(Q(p,n)),b=logUnit(Q(2));return [add(a[0],mul(Q(e),b[0])),add(a[1],mul(Q(e),b[1]))];}
function actualWeights(m){const scale=100000000n,loEta=Q(4057,100000),hiEta=Q(4149,100000),w=[];for(let p=2;p*6<m;p++){if(!isPrime(p))continue;const logs=logBounds(p);for(let n=p;n*6<m;n*=p){let [a,b]=residual(n,m);let es=rangeQ([add(a,mul(b,loEta)),add(a,mul(b,hiEta))]);let t=rangeQ(es.flatMap(e=>logs.map(l=>neg(mul(e,l)))));let l=fl(mul(Q(scale),t[0])),h=ce(mul(Q(scale),t[1]));if(l!==0n||h!==0n)w.push({n,l,h});}}return w;}
function mulInterval(a,b,c,d){if(a>=0n){if(c>=0n)return [a*c,b*d];if(d<=0n)return [b*c,a*d];return [b*c,b*d];}if(b<=0n){if(c>=0n)return [a*d,b*c];if(d<=0n)return [b*d,a*c];return [a*d,a*c];}if(c>=0n)return [a*d,b*d];if(d<=0n)return [b*c,a*c];let ac=a*d,bc=b*c,ad=a*c,bd=b*d;return [ac<bc?ac:bc,ad>bd?ad:bd];}
function fibers(q,k,w){let L=w.map(z=>{let a=Array(q).fill(0n);a[0]=z.l;return a;}),H=w.map(z=>{let a=Array(q).fill(0n);a[0]=z.h;return a;});for(let j=1;j<k;j++){let LL=w.map(()=>Array(q).fill(0n)),HH=w.map(()=>Array(q).fill(0n));for(let i=0;i<w.length;i++)for(let b=0;b<q;b++){let lo=L[i][b],hi=H[i][b];if(lo===0n&&hi===0n)continue;for(let a=0;a<w.length;a++){let s=(b+w[i].n*w[a].n)%q,[v,u]=mulInterval(lo,hi,w[a].l,w[a].h);LL[a][s]+=v;HH[a][s]+=u;}}L=LL;H=HH;}return Array.from({length:q},(_,a)=>[L.reduce((s,v)=>s+v[a],0n),H.reduce((s,v)=>s+v[a],0n)]);}
function regression(){let counts={pointwise:0,l2:0,mass:0,intervalProducts:0},seed=13;function rng(){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed;}for(let a=-4;a<=4;a++)for(let b=a;b<=4;b++)for(let c=-4;c<=4;c++)for(let d=c;d<=4;d++){let z=mulInterval(BigInt(a),BigInt(b),BigInt(c),BigInt(d)),v=[a*c,a*d,b*c,b*d];if(z[0]!==BigInt(Math.min(...v))||z[1]!==BigInt(Math.max(...v)))throw Error("interval multiplication");counts.intervalProducts++;}
for(const q of [2,3,5,7,11,17,23])for(const k of [3,5,7])for(let test=0;test<12;test++){let w=Array.from({length:q},(_,n)=>{let t=BigInt(rng()%9)-4n;return {n,l:t,h:t};});let f=fibers(q,k,w),m=w.reduce((s,z)=>s+z.l,0n),B=w.reduce((s,z)=>{let a=z.l<0n?-z.l:z.l;return a>s?a:s;},0n),P=BigInt(q),pow=m**BigInt(k),sum=f.reduce((s,z)=>s+z[0],0n);if(sum!==pow||f.some(z=>z[0]!==z[1]))throw Error("mass identity");counts.mass++;let l2=0n;for(const [a] of f){let r=P*a-pow;if((r<0n?-r:r)>P**BigInt((k+3)/2)*B**BigInt(k))throw Error("pointwise bound");counts.pointwise++;l2+=r*r;}if(l2>P*BigInt(q-1)*P**BigInt(k+1)*B**BigInt(2*k))throw Error("l2 bound");counts.l2++;}return counts;}
function run(){const counts=regression(),actual=[];for(const m of [64,128,256,512]){let q=nextPrime(m),w=actualWeights(m);for(const k of [5,7]){let f=fibers(q,k,w),negative=f.filter(z=>z[1]<0n).length,positive=f.filter(z=>z[0]>0n).length,a=f.findIndex(z=>z[1]<0n);actual.push({m,q,k,support:w.length,negative,positive,undetermined:q-negative-positive,firstNegative:a});}}
const primes=[2,3,5,7],Qw=primes.reduce((s,p)=>s*BigInt(p*p),1n),M=primes.reduce((s,p)=>s*BigInt((p-1)*(p-1)),1n);let k=9,dominates=M**BigInt(k)>(2n*Qw)**BigInt((k+3)/2);if(!dominates)throw Error("Euler model inequality");return {counts,actual,eulerCountermodel:{Q:Qw.toString(),M:M.toString(),k,dominates}};}
console.log(JSON.stringify(run(), null, 2));
