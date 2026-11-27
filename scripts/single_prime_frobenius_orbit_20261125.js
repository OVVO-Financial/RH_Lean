// Exact-integer physical prime-power orbit and boundary diagnostic.
// Run: node scripts/single_prime_frobenius_orbit_20261125.js
'use strict';
function primeOrbitAudit() {
  const assert = (b, msg) => { if (!b) throw new Error(msg); };
  const primes = [2,3,5,7,11,13,17];
  const gcd = (a,b) => { while (b) [a,b]=[b,a%b]; return a; };
  const add = (m,k,v=1) => m.set(k,(m.get(k)||0)+v);
  const val = (m,k) => m.get(k)||0;
  function audit(L,U,P,p) {
    const A=new Map(), items=[];
    for(let n=L;n<=U;n++) if(gcd(n,P)===1){add(A,n%P);items.push(n);}
    const layers=[];
    let checks=0, violations=0, maxNumerator=0, removed=0, odd=0, even=0, exactOdd=0;
    for(let k=1,d=p;d<=U;k++,d*=p){
      const D=new Map(), C=new Map(), DA=new Map(), exactWeights=new Map(), pulledWeights=new Map();
      for(const n of items) if(n%d===0){add(D,n%P);add(DA,(n/d)%P);add(exactWeights,(n/d)%P,n);}
      for(let m=Math.ceil(L/d);m<=Math.floor(U/d);m++)if(gcd(m,P)===1){add(C,m%P);add(pulledWeights,m%P,d*m);}
      const predictedTargets=new Map();
      for(const [s,a] of A) predictedTargets.set((d*s)%P,a);
      const all=new Set([...A.keys(),...D.keys(),...predictedTargets.keys()]);
      for(const t of all){
        const actual=val(D,t), own=val(A,t), src=val(predictedTargets,t);
        assert(Math.abs(d*actual-own)<d,"CRT floor/ceil");
        assert(Math.abs(own-src)<=1,"interval fibre balance");
        assert(Math.abs(d*actual-src)<=d,"source-to-destination rounding");
        checks++;
        if(d*actual>src) violations++;
        maxNumerator=Math.max(maxNumerator,Math.abs(d*actual-src));
      }
      for(const s of new Set([...C.keys(),...DA.keys()])){
        assert(val(C,s)===val(DA,s),"cofactor count");
        assert(val(exactWeights,s)===val(pulledWeights,s),"weighted cofactor count");
        assert(val(C,s)===val(D,(d*s)%P),"orbit transport");
      }
      const mass=[...D.values()].reduce((a,b)=>a+b,0);
      if(k===1)removed=mass;
      if(k%2===1)odd+=mass;else even+=mass;
      layers.push({k,d,mass});
    }
    for(const n of items){let m=n,v=0;while(m%p===0){m/=p;v++;}if(v%2)exactOdd++;}
    assert(odd-even===exactOdd,"odd/even cumulative depth difference");
    return {checks,violations,maxNumerator,removed,odd,even,exactOdd,A:[...A].sort((a,b)=>a[0]-b[0]),layers};
  }
  const first=audit(900,929,30,7), second=audit(930,959,30,7);
  assert(JSON.stringify(first.A)===JSON.stringify(second.A),"identical old populations");
  assert(first.removed===1&&second.removed===2,"physical difference");
  const totals={blocks:0,checks:0,naiveCapViolations:0,primePowerLayers:0};
  let P=1;
  for(const p of primes){
    for(let r=p;r<=128;r++){
      const x=audit(r*r,(r+1)*(r+1)-1,P,p);
      totals.blocks++;totals.checks+=x.checks;totals.naiveCapViolations+=x.violations;totals.primePowerLayers+=x.layers.length;
    }
    P*=p;
  }
  return {first,second,totals};
}
console.log(JSON.stringify(primeOrbitAudit(),null,2));
