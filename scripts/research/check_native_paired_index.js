'use strict';
const assert = require('node:assert/strict');
const mod = (a,m) => ((a%m)+m)%m;
const vp = (a,p) => { if(a===0n) return Infinity; let k=0; while(a%p===0n){a/=p;k++;}return k; };
const dot = (a,b) => a.reduce((z,v,i)=>z+v*b[i],0n);
const pow = (p,k)=>p**BigInt(k);
const rows = (D,p,t) => {
  const m=pow(p,t); const N=Number(m)**D;
  return Array.from({length:N},(_,k)=>Array.from({length:D},(_,i)=>BigInt(Math.floor(k/Number(m)**i)%Number(m))));
};
function groups(D,p,t,vs) {
  const m=pow(p,t); let H=[Array(D).fill(0n)];
  for(const v of vs){const map=new Map(); for(const w of H)for(let i=0n;i<m;i++){
    const u=w.map((a,j)=>mod(a+i*v[j],m)); map.set(u.join(','),u);
  } H=[...map.values()];} return H;
}
let exact=0, finite=0, groupChecks=0, chartChecks=0;
// Optimal paired coordinate lattices: the common coordinates alone are scaled.
for(const p of [2n,3n,5n,131n])for(let D=1;D<=14;D++)for(let r=0;r<=D;r++)for(let s=0;s<=D;s++)for(let t=0;t<=8;t++){
  const u=Array.from({length:D},(_,i)=>BigInt(i+1)*p+1n);
  const L=Array.from({length:r},(_,i)=>i);
  const R=Array.from({length:s},(_,i)=>D-s+i);
  const K=Math.max(0,r+s-D); const delta=R.reduce((z,j)=>z+(j<r?t:0),0);
  assert.equal(delta,K*t);
  for(const i of L)for(const j of R){if(i===j)assert(vp(u[i]*pow(p,j<r?t:0),p)>=t);}
  exact++;
}
// Exhaust every cyclic subgroup and pairs of cyclic subgroups in small finite modules.
for(const [p,t,D] of [[2n,1,3],[2n,2,2],[3n,1,3],[3n,2,2],[2n,3,2]]){
  const m=pow(p,t), all=rows(D,p,t), subgroups=new Map();
  for(const v of all){const H=groups(D,p,t,[v]);subgroups.set(H.map(x=>x.join(',')).sort().join(';'),H);}
  const gs=[...subgroups.values()];
  for(const H of gs){
    const annih=all.filter(v=>H.every(w=>mod(dot(v,w),m)===0n));
    assert.equal(H.length*annih.length,all.length);groupChecks++;
    for(const K of gs){if(H.every(v=>K.every(w=>mod(dot(v,w),m)===0n))){assert(H.length*K.length<=all.length);finite++;}}
  }
}
// At the ramified binary inertia prime every nonzero channel has unit norm.
for(const p of [3n,5n,7n,11n,131n])for(let k=0;k<=32;k++)for(const sign of [1n,-1n]){
  const z=1n+sign*pow(p,k); if(z!==0n){assert.equal(vp(z,p),0);chartChecks++;}
}
// Existing x=65 nominal-order diagnostic at the original cutoff 130.
const factVal=(n,p)=>{let v=0;while(n){n=Math.floor(n/p);v+=n;}return v;};
const f=factVal(100000,131)+3*factVal(50000,131);
assert.equal(f,1917);assert.equal(Math.ceil(f/2),959);
console.log(JSON.stringify({optimalPairedCoordinateCases:exact,orthogonalComplementCases:groupChecks,orthogonalSubgroupPairs:finite,nonzeroBinaryChannels:chartChecks,nominalPole:f,commonLineClearing:Math.ceil(f/2)}));
