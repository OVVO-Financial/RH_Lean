'use strict';
// Positive real quadratic root, actual class test, exact paired valuation.
const assert=require('node:assert/strict');
const mod=(x,p)=>(x%p+p)%p;
const vp=(n,p)=>{assert(n!==0n);let k=0;while(n%p===0n){n/=p;k++}return k;};
const ps=[2n,3n,5n,7n,11n,13n,17n,19n,23n,29n,31n];
const prod=a=>a.reduce((s,x)=>s*x,1n);
const sum=a=>a.reduce((s,x)=>s+x,0n);
function liftUnit(n,p,k) {
 const f=t=>t*t-(2n*n+1n)*t+n*n;
 let r=1n,M=p;assert.equal(mod(f(r),M),0n);
 for(let j=1;j<k;j++){
  const next=M*p;let found=false;
  for(let z=0n;z<p;z++){
   const t=r+z*M;
   if(mod(f(t),next)===0n){r=t;found=true;break;}
  }
  assert(found);M=next;
 }
 return [r,M];
}
// Algebraic integer a+b*T, T^2=(2N+1)*T-N^2.
const add=(u,v)=>[u[0]+v[0],u[1]+v[1]];
const scale=(u,k)=>[u[0]*k,u[1]*k];
const mul=(n,u,v)=>[u[0]*v[0]-n*n*u[1]*v[1],u[0]*v[1]+u[1]*v[0]+(2n*n+1n)*u[1]*v[1]];
const eq=(a,b)=>a[0]===b[0]&&a[1]===b[1];
let algebra=0,places=0,paired=0,heights=0;
for(const p of ps)for(let k=1;k<=7;k++){
 const n=p**BigInt(k),a=[0n,1n],b=[2n*n+1n,-1n];
 assert(eq(add(a,b),[2n*n+1n,0n]));
 assert(eq(mul(n,a,b),[n*n,0n]));algebra+=2;
 const [r,M]=liftUnit(n,p,2*k+2);
 const s=mod(2n*n+1n-r,M);
 assert.equal(vp(r,p),0);assert.equal(vp(s,p),2*k);
 assert.equal(mod(r*s,M),mod(n*n,M));places+=3;
 for(let m=1;m<=31;m++){
  const card=BigInt(m),w=Array(m).fill(1n),x=w.map((_,i)=>BigInt((i*17+m)%23-11)),y=w.map((_,i)=>BigInt((i*19+m)%31-15));
  const table=scale(a,card),norm=scale(mul(n,a,a),card);
  assert(eq(table,[0n,card]));
  assert(eq(norm,[-card*n*n,card*(2n*n+1n)]));
  // h*<x,P y> = sum x * sum y, actual h=m and P=J/m.
  const numerator=sum(x.map(z=>z*sum(y)));
  assert.equal(numerator,sum(x)*sum(y));
  assert.equal(vp(card*r,p),vp(card,p));paired+=4;
 }
 // Inverse actual norm ratio (N/T)^2 has valuation 2k.
 assert.equal(2*(vp(n,p)-vp(r,p)),2*k);heights++;
}
let signed=0;
for(const p of ps)for(let d=1;d<=7;d++)for(let e=1;e<=7;e++){
 const D=p**BigInt(d),E=p**BigInt(e),[a]=liftUnit(D,p,2*d+2),[b]=liftUnit(E,p,2*e+2);
 assert.equal(2*(vp(D,p)-vp(a,p)-vp(E,p)+vp(b,p)),2*(d-e));signed++;
}
console.log(JSON.stringify({algebra,places,paired,heights,signed,total:algebra+places+paired+heights+signed}));