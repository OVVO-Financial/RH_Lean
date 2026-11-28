'use strict';
// Exact direct test of the paired-depth Selmer analogue.
const assert=require('node:assert/strict');
const abs=x=>x<0n?-x:x;
function gcd(a,b){a=abs(a);b=abs(b);while(b){[a,b]=[b,a%b]}return a;}
const sum=a=>a.reduce((s,x)=>s+x,0n),prod=a=>a.reduce((s,x)=>s*x,1n);
const ps=[3n,5n,7n,11n,13n,17n,19n,23n];
let seed=0x4321abcd;function rnd(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n;}
const coeffs=a=>a.reduce((v,[d,e])=>v.flatMap(z=>[z*d,z*e]),[1n]);
let gap=0,swap=0,coeff=0,projection=0,retraction=0;
for(let d=1;d<=8;d++)for(let s=0;s<80;s++){
 const beta=ps.slice(0,d).map(()=>rnd(6)),alpha=beta.map(()=>rnd(6));
 const D=beta.map((e,i)=>ps[i]**BigInt(e)),E=alpha.map((e,i)=>ps[i]**BigInt(e));
 const g=D.map((v,i)=>gcd(v,E[i])),U=D.map((v,i)=>(v>E[i]?v:E[i])/g[i]),S=prod(U.map(u=>1n+u*u));
 const C=prod(g),M=prod(D.map((v,i)=>v>E[i]?v:E[i]));
 const a=coeffs(D.map((v,i)=>[v,E[i]]));
 assert.equal(a.reduce(gcd,0n),C);assert(a.includes(C));
 assert.equal(sum(a.map(v=>v*v)),C*C*S);
 assert(M*M<=C*C*S&&C*C*S<=2n**BigInt(d)*M*M);
 coeff+=4;
 const v=coeffs(U.map(u=>[1n,u]));
 assert.equal(v[0],1n);assert.equal(sum(v.map(z=>z*z)),S);coeff+=2;
 for(const u of U){
   const q=1n+u*u,b=BigInt(rnd(11)-5),k=BigInt(rnd(11)-5),a=b+q*k;
   const A=b+k,B=u*k,C=b+u*u*k;
   assert.equal(A+u*B,a);assert.equal(B+u*C,u*a);
   assert.equal(-u*A+B,-u*b);assert.equal(-u*B+C,b);
   assert.equal((a-b)%q,0n);gap+=5;
   assert.equal(gcd(1n-u*u,q),2n);swap++;
   assert.equal(q%8n,2n);swap++;
 }
 const H=BigInt(1+rnd(50)),z=v.map(()=>BigInt(rnd(7)-3));
 z[0]=H-sum(z.slice(1).map((w,i)=>w*v[i+1]));
 assert.equal(sum(z.map((w,i)=>w*v[i])),H);
 assert(S*sum(z.map(w=>w*w))>=S);retraction+=2;
 const unit=v.map((_,i)=>i===0?1n:0n);
 assert.equal(sum(unit.map((w,i)=>w*v[i])),1n);assert.equal(S*sum(unit.map(w=>w*w)),S);retraction+=2;
 // Reduced denominator of the primitive pivot entry 1/S is S.
 assert.equal(S/gcd(1n,S),S);projection++;
 // Test arbitrary common scalars against every actual exterior entry.
 const h=BigInt(1+rnd(13)),m=BigInt(rnd(17))*S+(s%2===0?0n:1n);
 const expected=(h*m)%S===0n;
 let all=true;
 for(const x of v)for(const y of v){if((h*m*x*y)%S!==0n)all=false;}
 assert.equal(all,expected);projection++;
}
console.log(JSON.stringify({gap,swap,coeff,projection,retraction,total:gap+swap+coeff+projection+retraction}));