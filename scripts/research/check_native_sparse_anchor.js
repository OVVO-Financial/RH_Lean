// Native sparse anchor: exact integer/rational determinant and physical dual regression.
'use strict';
const assert=require('node:assert/strict');
const ps=[3n,5n,7n,11n,13n,17n,19n], ls=[2n,3n,5n,7n,11n,13n,17n,19n,23n,29n,31n];
const sum=a=>a.reduce((s,x)=>s+x,0n), prod=a=>a.reduce((s,x)=>s*x,1n);
const abs=x=>x<0n?-x:x;
function gcd(a,b){a=abs(a);b=abs(b);while(b){[a,b]=[b,a%b]}return a}
function rat(n,d=1n){assert(d!==0n);if(d<0n){n=-n;d=-d}const g=gcd(n,d);return [n/g,d/g]}
const add=(a,b)=>rat(a[0]*b[1]+b[0]*a[1],a[1]*b[1]), mul=(a,b)=>rat(a[0]*b[0],a[1]*b[1]), div=(a,b)=>rat(a[0]*b[1],a[1]*b[0]);
const eq=(a,b)=>a[0]*b[1]===b[0]*a[1], le=(a,b)=>a[0]*b[1]<=b[0]*a[1];
const rsum=a=>a.reduce(add,rat(0n)), rprod=a=>a.reduce(mul,rat(1n)), rpow=(a,k)=>rat(a[0]**BigInt(k),a[1]**BigInt(k));
const mat=(d,e,f)=>Array.from({length:d},(_,i)=>Array.from({length:e},(_,j)=>f(i,j)));
function det(A){if(!A.length)return 1n;let M=A.map(r=>r.slice()),sg=1n,den=1n;for(let i=0;i<M.length-1;i++){if(!M[i][i]){let j=i+1;while(j<M.length&&!M[j][i])j++;if(j===M.length)return 0n;[M[j],M[i]]=[M[i],M[j]];sg=-sg}let v=M[i][i];for(let j=i+1;j<M.length;j++)for(let k=i+1;k<M.length;k++){let t=v*M[j][k]-M[j][i]*M[i][k];assert.equal(t%den,0n);M[j][k]=t/den}for(let j=i+1;j<M.length;j++)M[j][i]=0n;den=v}return sg*M.at(-1).at(-1)}
const gram=(A,n)=>mat(A[0].length,A[0].length,(i,j)=>sum(A.map((r,k)=>n[k]*r[i]*r[j])));
const q=(D,j)=>prod(D.filter((_,i)=>i!==j));
const ind=(a,b)=>a===b?1n:0n;
const test=(D,n,j,k,i)=>rat(ind(i,k+1)-ind(j,k+1),n[i]*D[i]);
const star=(D,i,k)=>D[i]*(ind(i,k+1)-ind(i,0));
const amp=(D,j)=>mat(D.length,D.length,(i,k)=>k===0?ind(i,j):star(D,i,k-1));
function val(n,p){assert(n!==0n);let e=0;while(n%p===0n){n/=p;e++}return e}
const rv=(a,p)=>val(a[0],p)-val(a[1],p);
let seed=0x91872615;function rand(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>8)%n}
let determinants=0,pairings=0,energies=0,local=0,global=0;
for(let d=1;d<=7;d++)for(let t=0;t<60;t++){
 const P=ps.slice(0,d), b=P.map(()=>rand(6)),a=P.map(()=>rand(6)),D=P.map((p,i)=>p**BigInt(b[i])),E=P.map((p,i)=>p**BigInt(a[i])),M=D.map((v,i)=>v>E[i]?v:E[i]), n=P.map(()=>BigInt(4+rand(40))), f=D.map((v,i)=>rat(v,E[i])), R=rprod(f), omitted=[];
 for(let j=0;j<d;j++){
  const Rj=rat(q(D,j),q(E,j));omitted.push(Rj);assert(eq(mul(Rj,f[j]),R));global++;
  for(const B of [D,E,M]){
   const A=amp(B,j), H=gram(A,n);assert.equal(det(A),q(B,j));assert.equal(det(H),prod(n)*q(B,j)**2n);determinants+=2;
   const W=H[0][0];assert.equal(W,n[j]);const K=H.slice(1).map((r,i)=>r.slice(1).map((v,k)=>W*v-H[i+1][0]*H[0][k+1]));
   // det(K) = W^rank det(Schur); use the omitted-layer closed form.
   assert.equal(det(K),W**BigInt(d-1)*prod(n.filter((_,i)=>i!==j))*q(B,j)**2n);determinants++;
   let trace=rat(0n), mn=n.reduce((u,v)=>u<v?u:v);
   for(let k=0;k<d-1;k++){
    for(let l=0;l<d-1;l++){
     const dot=rsum(n.map((v,i)=>mul(rat(v*star(B,i,l)),test(B,n,j,k,i))));
     assert(eq(dot,rat(ind(k,l))));pairings++;
    }
    const energy=rsum(n.map((v,i)=>mul(rat(v),rpow(test(B,n,j,k,i),2))));
    assert(le(energy,rat(BigInt(d),mn)));trace=add(trace,energy);energies++;
   }
   assert(le(trace,rat(BigInt(Math.max(0,2*d-3)),mn)));energies++;
  }
 }
 assert(eq(rprod(omitted),rpow(R,d-1)));global++;
 for(const p of ls){
  const index=P.indexOf(p),j=index<0?0:index, N=n.map(v=>v%p===0n?v-1n:v);
  assert.equal(rv(omitted[j],p),0);assert.equal(rv(R,p),index<0?0:b[index]-a[index]);global+=2;
  for(const B of [D,E,M]){
   assert(det(amp(B,j))%p!==0n);assert(det(gram(amp(B,j),N))%p!==0n);local+=2;
   for(let k=0;k<d-1;k++)for(let i=0;i<d;i++){
    const z=test(B,N,j,k,i);assert(z[1]%p!==0n);local++;
   }
  }
 }
}
console.log(JSON.stringify({determinants,pairings,energies,local,global,total:determinants+pairings+energies+local+global}));