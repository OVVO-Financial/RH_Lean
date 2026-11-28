'use strict';
// Exact Gaussian phase fitting, with conjugate repayment at each odd pole.
const assert=require('node:assert/strict');
function factors(n){let a=[];for(let p=2n;p*p<=n;p++)if(n%p===0n){let k=0;while(n%p===0n){n/=p;k++;}a.push([p,k]);}if(n>1n)a.push([n,1]);return a;}
function vp(n,p){if(n===0n)throw Error('zero valuation');let k=0;while(n%p===0n){n/=p;k++;}return k;}
const mod=(n,p)=>(n%p+p)%p;
let cases=0, identities=0;
for(let u=1n;u<=801n;u+=2n){
 const S=1n+u*u;assert.equal(S%8n,2n);
 let odd=1n;
 for(const [p,k] of factors(S)){
  if(p===2n){assert.equal(k,1);continue;}
  assert.equal(p%4n,1n);
  const q=p**BigInt(k),modulus=q*p;
  // i=-u mod p^k, lift one more digit to the chosen embedding.
  let root=null;
  for(let j=0n;j<p;j++){
    const x=mod(-u+j*q,modulus);
    if((x*x+1n)%modulus===0n){root=x;break;}
  }
  assert(root!==null);
  // Avoid a literal zero in the finite representative.
  const vplus=vp(u+root+modulus,p),vminus=vp(u-root+modulus,p);
  assert.equal(vplus,k);assert.equal(vminus,0);
  assert.equal(vplus-vminus,k);assert.equal(vminus-vplus,-k);
  // Both the chosen Gaussian scalar and its conjugate cannot clear the pole.
  assert.equal(Math.max(k-(vplus-vminus),k-(vminus-vplus)),2*k);
  odd*=q;cases++;identities+=6;
 }
 assert.equal(2n*odd,S);identities+=2;
}
console.log(JSON.stringify({phasePlaceCases:cases,exactChecks:identities}));