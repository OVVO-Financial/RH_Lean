'use strict';
// Run: node scripts/single_prime_euler_defect_20261125.js [R ...]
// Integer telescoping is exact BigInt arithmetic. Weighted diagnostics use binary64.
function diagnose(R) {
  const N = R*R-1, spf = new Uint32Array(N+1), primes = [];
  for (let n=2; n<=N; ++n) {
    if (spf[n]!==0) continue;
    primes.push(n);
    for(let j=n;j<=N;j+=n) if(spf[j]===0) spf[j]=n;
  }
  const w = n => Math.log(n)*(N/n-1);
  const check = (b,msg) => { if(!b) throw Error(`R=${R}: ${msg}`); };
  const near = (a,b) => Math.abs(a-b)<=2e-10*Math.max(1,Math.abs(a),Math.abs(b));
  let baseline=0, debt=0, absDebt=0, primeCapacity=0, composite=0, initial=0;
  let positive=0, negative=0, zero=0, steps=0, maxCofactors=0;
  for(let r=1;r<R;++r){
    const lo=Math.max(2,r*r), hi=(r+1)*(r+1)-1, L=hi-lo+1;
    const counts=new Map(), weights=new Map();
    let A=0, actual=0, survivors=0;
    for(let n=lo;n<=hi;++n){
      const v=w(n), p=spf[n]; A+=v;
      if(p===n){actual+=v;survivors++;}
      else{
        check(p<=r,`uncovered composite ${n}`);
        counts.set(p,(counts.get(p)||0)+1);
        weights.set(p,(weights.get(p)||0)+v);
        composite+=v;
      }
    }
    let a=L, aw=A, P=1n, phi=1n, D=0n, v=1, dw=0, adw=0;
    for(const p of primes){
      if(p>r)break;
      const c=counts.get(p)||0, cw=weights.get(p)||0;
      let cp=0, cwp=0;
      for(let m=Math.ceil(lo/p);m<=Math.floor(hi/p);++m){
        if(m===1 || spf[m]>=p){cp++;cwp+=w(p*m);}
      }
      check(cp===c && near(cwp,cw),`cofactor reindex r=${r} p=${p}`);
      maxCofactors=Math.max(maxCofactors,cp);
      const numerator=BigInt(p*c-a), delta=cw-aw/p, f=1-1/p;
      if(numerator>0n)positive++;else if(numerator<0n)negative++;else zero++;
      D=BigInt(p-1)*D+numerator*P; P*=BigInt(p); phi*=BigInt(p-1);
      a-=c; aw-=cw; v*=f; dw=f*dw+delta; adw=f*adw+Math.abs(delta);steps++;
      check(BigInt(a)*P===BigInt(L)*phi-D,`integer telescoping r=${r} p=${p}`);
    }
    check(a===survivors && near(aw,actual),`prime survivors r=${r}`);
    check(near(v*A-dw,actual),`weighted telescoping r=${r}`);
    baseline+=v*A; debt+=dw; absDebt+=adw; primeCapacity+=actual; initial+=A;
  }
  let cTruncated=0, properPowers=0;
  for(const p of primes){
    cTruncated+=Math.log(p)/(p*(p-1));
    for(let power=p*p; power<=N; power*=p)
      properPowers+=Math.log(p)*(N/power-1);
  }
  const gamma=0.5772156649015329, main=N*Math.log(N)-(1+gamma+cTruncated)*N;
  const centered=debt-(baseline-main), G=primeCapacity+properPowers-N*Math.log(N)+(1+gamma)*N;
  const properError=N*cTruncated-properPowers;
  const tol=2e-10*Math.max(1,initial);
  check(Math.abs(initial-composite-primeCapacity)<=tol,'capacity conservation');
  check(Math.abs(baseline-debt-primeCapacity)<=tol,'global telescoping');
  check(Math.abs(-centered-properError-G)<=tol,'centered terminal source identity');
  return {R,N,steps,positive,negative,zero,maxCofactors,
    baseline,debt,absDebt,primeCapacity,centeredDefect:centered,
    properPowerErrorTruncated:properError,G,
    driftOverNLogN:debt/(N*Math.log(N)),absoluteToNet:absDebt/Math.abs(debt)};
}
const Rs=process.argv.length>2?process.argv.slice(2).map(Number):[16,32,64,317,1027];
for(const R of Rs){if(!Number.isSafeInteger(R)||R<2||R>10000)throw Error('R must be an integer in [2,10000]');console.log(JSON.stringify(diagnose(R)));}
