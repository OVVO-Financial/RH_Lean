// Exact integer-scaled valuation tests. No approximation or zeta assumption.
"use strict";
let checks = 0, sharp = 0, multiplicity = 0;
for (let r=1; r<=24; ++r) for (let seed=0; seed<31; ++seed) {
  const s=Array.from({length:r}, (_,i)=>((seed*13+i*17+i*i*3)%25)-12);
  const T=s.reduce((a,b)=>a+b,0);
  const target=s.reduce((a,x)=>a+Math.abs(r*x-T),0);
  const f=A=>s.reduce((a,x)=>a+Math.max(0,-A-r*x),0);
  for (let A=-39*r; A<=39*r; A+=Math.max(1,r-1)) {
    const B=-2*T-A;
    if (f(A)+f(B)<target) throw Error("paired phase inequality");
    ++checks;
  }
  if (2*f(-T)!==target) throw Error("balanced sharpness");
  ++sharp;
}
for (let r=1; r<=64; ++r) for (let m=0; m<=r; ++m)
  for (let v=-24; v<=24; ++v) {
    const T=m*v;
    if (m*Math.abs(r*v-T)+(r-m)*Math.abs(T)!==2*m*(r-m)*Math.abs(v))
      throw Error("multiplicity");
    ++multiplicity;
  }
console.log({pairedPhaseChecks:checks,sharpBalanceChecks:sharp,multiplicityChecks:multiplicity});
