'use strict';
// Actual physical-site, cofactor and weighted signed-ledger diagnostic.
// Run: node scripts/single_prime_weighted_recovery_20261125.js [R ...]
function runNativeRecovery(R) {
  if(!Number.isSafeInteger(R)||R<3||R>2048)throw Error("R must be an integer in [3,2048]");
  const N=R*R-1, primes=[], sieve=new Uint16Array(N+1);
  for(let p=2;p<R;p++)if(!sieve[p]){primes.push(p);for(let n=p;n<=N;n+=p)if(!sieve[n])sieve[n]=p;}
  const V=new Float64Array(R);let v=1;for(let s=1;s<R;s++){if(sieve[s]===s)v*=1-1/s;V[s]=v;}
  const block=new Uint16Array(N+1), U=new Float64Array(N+1), W=new Float64Array(N+1), logN=Math.log(N);
  for(let s=1;s<R;s++)for(let n=s*s;n<(s+1)*(s+1);n++)block[n]=s;
  let HN=0,HR=0;for(let n=1;n<=N;n++){U[n]=N/n-1;W[n]=Math.log(n)*U[n];HN+=1/n;if(n<R)HR+=1/n;}
  let countChecks=0, pointChecks=0, signedChecks=0, maxRelError=0, weightedHalfViolations=0, siteHalfViolations=0, jointTests=0,jointFailures=0;
  const byPrime=[], sum={rawDefect:0,strippedDefect:0,pureCorrection:0,lowCredit:0,logGain:0,cutoffLoss:0,attenuationLoss:0,normalizationLoss:0,physicalDeep:0,referenceDeep:0,tailUpper:0,physicalMass:0,closureMass:0};
  function near(a,b,scale,label){const err=Math.abs(a-b)/Math.max(1,scale);maxRelError=Math.max(maxRelError,err);if(err>2e-10)throw Error(label+" "+a+" != "+b+" at R="+R);}
  for(const p of primes){
    const pure=new Set();for(let n=p;n<=N;n*=p)pure.add(n);
    const alpha=n=>V[Math.max(p,block[n])]/V[p];
    const allowed=n=>n>=p&&(!sieve[n]||sieve[n]>=p)&&!pure.has(n);
    let rawA=0,A=0,Aplus=0,L=0,Aplus0=0,pureA=0;
    const dSite=new Uint32Array(R), bSite=[], rows=[];
    let K=1,Q=p;while(Q<R*p){Q*=p;K++;}
    for(let k=1,d=p;d<=N||k===1;k++,d*=p)rows.push({k,d,C:0,C0:0,rawC:0,lg:0,top:0,loss:0,norm:0,cofactor:0});
    for(let n=p;n<=N;n++){
      const a=alpha(n),rough=!sieve[n]||sieve[n]>=p;
      if(!rough)continue;
      if(n>=p*p)rawA+=a*W[n];
      if(pure.has(n)){if(n>=p*p)pureA+=a*W[n];}
      else {Aplus+=a*W[n];Aplus0+=a*U[n];if(n<p*p)L+=a*W[n];else {A+=a*W[n];dSite[block[n]]++;}}
      if(n>=p*p&&sieve[n]===p){
        let m=n;
        for(let j=0;m%p===0;j++){
          m/=p;const row=rows[j];row.rawC+=a*W[n];
          if(pure.has(n))continue;
          if(!allowed(m)||row.d*m!==n||N-n>N-m)throw Error("exact cofactor/scaling failed");
          row.C+=a*W[n];row.C0+=a*U[n];pointChecks++;
          if(a*W[n]>(row.k+1)*alpha(m)*W[m]/row.d+2e-10*Math.max(1,W[n]))throw Error("weighted scaling");
          if(!bSite[j])bSite[j]=new Uint32Array(R);bSite[j][block[n]]++;
        }
      }
    }
    near(Aplus,A+L,Aplus,"closure split");near(rawA,A+pureA,rawA,"raw capacity split");
    for(let s=p;s<R;s++){
      const d=dSite[s];
      for(let j=0;j<bSite.length;j++){const b=bSite[j][s];if(!b)continue;
        if(b>d)throw Error("physical rank");countChecks++;
        if(2**(j+1)*b>d)siteHalfViolations++;
        for(let i=0;i<j;i++){const bi=bSite[i][s];if(bi<b)throw Error("nested ranks");jointTests++;if(d*b>bi*b)jointFailures++;}
      }
    }
    for(const row of rows){
      const {k,d}=row;
      for(let m=p;m<=N;m++)if(allowed(m)){
        const am=alpha(m);
        if(m>Math.floor(N/d)){row.top+=am*W[m];continue;}
        const n=d*m,an=alpha(n);
        if(n<p*p||sieve[n]!==p)throw Error("actual owner");
        row.cofactor+=an*W[n];row.lg+=Math.log(d)*an*U[m];row.norm+=(d-1)*an*Math.log(n);row.loss+=(am-an)*W[m];
      }
      near(row.C,row.cofactor,row.C+row.cofactor,"cofactor sum");
      const scale=Aplus+d*row.C+row.lg+row.top+row.loss+row.norm;
      near(d*row.C-A,L+row.lg-row.top-row.loss-row.norm,scale,"signed layer");signedChecks++;
      if(row.C0>Aplus0/d+2e-10*Math.max(1,Aplus0))throw Error("harmonic contraction");
      if(row.C>(k+1)*Aplus/d+2e-10*Math.max(1,Aplus))throw Error("log contraction");
      if(p>=5&&row.C>2**(-k)*Aplus+2e-10*Math.max(1,Aplus))weightedHalfViolations++;
      if(k>=K)sum.physicalDeep+=row.rawC;
    }
    const row=rows[0],rawDelta=row.rawC-rawA/p,stripDelta=row.C-A/p,corr=(1-1/p)*pureA;
    near(rawDelta,stripDelta+corr,rawA+row.rawC,"pure correction");
    sum.rawDefect+=rawDelta;sum.strippedDefect+=stripDelta;sum.pureCorrection+=corr;
    sum.lowCredit+=L/p;sum.logGain+=row.lg/p;sum.cutoffLoss+=row.top/p;sum.attenuationLoss+=row.loss/p;sum.normalizationLoss+=row.norm/p;
    sum.referenceDeep+=rawA/(Q*(1-1/p));sum.tailUpper+=2*N*logN*HN/(R*(p-1));
    sum.physicalMass+=A;sum.closureMass+=Aplus;
    byPrime.push({p,K,depths:rows.length,carrier:Aplus,physical:A,low:L,first:row.C,rawDelta,stripDelta,correction:corr});
  }
  near(sum.rawDefect,sum.strippedDefect+sum.pureCorrection,Math.abs(sum.rawDefect)+Math.abs(sum.strippedDefect)+sum.pureCorrection,"raw global correction");
  near(sum.strippedDefect,sum.lowCredit+sum.logGain-sum.cutoffLoss-sum.attenuationLoss-sum.normalizationLoss,sum.lowCredit+sum.logGain+sum.cutoffLoss+sum.attenuationLoss+sum.normalizationLoss,"global signed ledger");
  const bound=2*R*logN*HN*HR;
  if(sum.physicalDeep+sum.referenceDeep>sum.tailUpper+1e-8||sum.tailUpper>bound+1e-8)throw Error("global deep bound");
  return {R,N,primes:primes.length,countChecks,pointChecks,signedChecks,maxRelError,weightedHalfViolations,siteHalfViolations,jointTests,jointFailures,deepBound:bound,sum,byPrime};
}
const scales=process.argv.length>2?process.argv.slice(2).map(Number):[64,317,1027];
console.log(JSON.stringify(scales.map(runNativeRecovery),null,2));
