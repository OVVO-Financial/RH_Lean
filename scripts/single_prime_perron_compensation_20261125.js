'use strict';
// Reproduce on actual square-block old-wheel populations; exact integer floor checks,
// binary64 weighted and complex phase consistency checks. Not a certified real enclosure.
function runPerronCompensation(R) {
  if(!Number.isSafeInteger(R)||R<3||R>2048)throw Error("R in [3,2048]");
  const N=R*R-1, Rtail=2*R,T=Rtail*Rtail-1;
  const sp=new Uint16Array(T+1),pr=[];
  for(let p=2;p<Rtail;p++)if(!sp[p]){pr.push(p);for(let n=p;n<=T;n+=p)if(!sp[n])sp[n]=p;}
  const V=new Float64Array(Rtail),root=new Uint16Array(T+1),W=new Float64Array(N+2),L=new Float64Array(T+1);
  let v=1;for(let r=1;r<Rtail;r++){if(sp[r]===r)v*=1-1/r;V[r]=v;for(let n=r*r;n<(r+1)*(r+1);n++){root[n]=r;L[n]=Math.log(n);if(n<=N)W[n]=L[n]*(N/n-1);}}
  const old=pr.filter(p=>p<R),J=Math.min(old.length,Math.floor(Math.log2(R))),tau=7/3;
  const cos=new Float64Array(N+1),sin=new Float64Array(N+1);
  for(let n=1;n<=N;n++){cos[n]=Math.cos(tau*L[n]);sin[n]=-Math.sin(tau*L[n]);}
  let floorChecks=0,hazardChecks=0,phaseChecks=0,crossingChecks=0,abelChecks=0,lowBoundViolations=0,raw=0,lowRaw=0,lowMainApprox=0,lowErrorBound=0,lowTailErrorBound=0,maxRelErr=0,lowMaxPrefixRatio=0;
  const rows=[];
  function near(a,b,scale,label){const e=Math.abs(a-b)/Math.max(1,scale);maxRelErr=Math.max(maxRelErr,e);if(e>2e-9)throw Error(label+" "+a+" != "+b+" R="+R);}
  let divs=[[1,1]];
  for(let i=0;i<old.length;i++){
    const p=old[i], B=2**i, a=n=>V[Math.max(p,root[n])]/V[p];
    const isOld=n=>!sp[n]||sp[n]>=p;
    const f=n=>(isOld(n)?(n%p===0?p-1:-1):0);
    const coeffR=new Float64Array(R),coeffI=new Float64Array(R);
    const before=p*p-1;
    let S=0,attS=0,priorHazard=0,direct=0,abel=0,totalAbs=0,maxPrefix=0;
    let re=0,im=0,refRe=0,refIm=0,clipRe=0,clipIm=0,dirJ=0,bandJ=0;
    let reH=0,imH=0,prevA=1;
    const cp=Math.cos(tau*L[p]),sip=-Math.sin(tau*L[p]);
    for(let r=p;r<R;r++){
      const lo=r*r,hi=(r+1)*(r+1)-1,ar=V[r]/V[p];
      if(ar!==prevA){priorHazard+=(prevA-ar)*S/p;reH+=(prevA-ar)*re;imH+=(prevA-ar)*im;prevA=ar;}
      for(let n=lo;n<=hi;n++){
        const t=f(n);S+=t;const e=t/p;
        attS+=ar*e;direct+=ar*e*W[n];totalAbs+=Math.abs(ar*e*W[n]);
        abel+=attS*(W[n]-W[n+1]);
        re+=e*cos[n];im+=e*sin[n];
        refRe+=ar*e*cos[n];refIm+=ar*e*sin[n];
        maxPrefix=Math.max(maxPrefix,Math.abs(S/p));
      }
      near(attS,ar*S/p+priorHazard,Math.abs(attS)+Math.abs(ar*S/p)+Math.abs(priorHazard),"hazard prefix");hazardChecks++;
      near(refRe,ar*re+reH,Math.abs(refRe)+Math.abs(ar*re)+Math.abs(reH)+hi,"phase hazard re");
      near(refIm,ar*im+imH,Math.abs(refIm)+Math.abs(ar*im)+Math.abs(imH)+hi,"phase hazard im");
      if(i<J){
        let fs=0;
        for(const [d,sgn] of divs) {
          const z=Math.floor(hi/d),z0=Math.floor(before/d);
          fs+=sgn*(z0%p-z%p);
        }
        if(fs!==S)throw Error("integer inclusion-exclusion prefix "+p+" "+r);
        floorChecks++;
      }
    }
    near(direct,abel,totalAbs,"weighted Abel");abelChecks++;
    // Independent exact twisted floor-scale identity on the complete physical
    // interval [p^2,N]. Source endpoints are [p, floor(N/p)].
    for(let n=p;n<=N;n++)if(isOld(n)){
      if(n>=p*p){clipRe+=cos[n];clipIm+=sin[n];}
      if(n<=Math.floor(N/p)){const rr=cos[n],ii=sin[n];
        coeffR[0]+=rr;coeffI[0]+=ii;
      }
    }
    near(re,cp*coeffR[0]-sip*coeffI[0]-clipRe/p,N,"centered Perron re");
    near(im,sip*coeffR[0]+cp*coeffI[0]-clipIm/p,N,"centered Perron im");
    phaseChecks++;
    // V3 J_{p,1}: evaluate the same old-wheel cofactor carrier in both
    // orders. Exclude pure p powers as required in the stripped ledger.
    const pure=new Set();for(let n=p;n<=N;n*=p)pure.add(n);
    const pref=new Float64Array(Math.floor(N/p)+1);
    for(let m=1;m<pref.length;m++){
      const eligible=m>=p&&isOld(m)&&!pure.has(m);
      const w=eligible?W[m]:0;
      pref[m]=pref[m-1]+w;
      if(eligible)dirJ+=(a(m)-a(p*m))*w;
    }
    for(let j=i+1;j<old.length;j++){
      const q=old[j],u=Math.min(pref.length-1,q*q-1),l=Math.floor((q*q-1)/p);
      if(u>=l)bandJ+=V[q-1]/(q*V[p])*(pref[u]-pref[l]);
    }
    near(dirJ,bandJ,dirJ+bandJ+1,"cross prime square bands");crossingChecks++;
    raw+=direct;
    if(i<J){
      if(maxPrefix>B+1e-9)throw Error("face interval cap");
      let c=0;for(let n=p*p;n<=T;n++){const t=f(n);if(t)c+=a(n)*(t/p)*L[n]/n;}
      const errBound=2*B*Math.log(N),tailBound=N*B*Math.log(T+1)/(T+1);
      const err=direct-N*c;
      if(Math.abs(err)>errBound+tailBound+1e-7)lowBoundViolations++;
      lowRaw+=direct;lowMainApprox+=N*c;lowErrorBound+=errBound;lowTailErrorBound+=tailBound;lowMaxPrefixRatio=Math.max(lowMaxPrefixRatio,maxPrefix/B);
      rows.push({p,faceBudget:B,maxPrefix,rawDefect:direct,mainAtFiniteT:N*c,centeredApprox:err,errorBound:errBound,truncationBound:tailBound});
      divs=divs.concat(divs.map(([d,s])=>[d*p,-s]));
    }
  }
  if(lowBoundViolations)throw Error("low centered bound violation");
  return {R,N,T,incomingPrimes:old.length,initialPrimeCount:J,lastLowPrime:old[J-1],floorChecks,hazardChecks,phaseChecks,crossingChecks,abelChecks,maxRelErr,lowBoundViolations,raw,lowRaw,lowMainApprox,lowCenteredApprox:lowRaw-lowMainApprox,lowErrorBound,lowTailErrorBound,lowMaxPrefixRatio,rows};
}
console.log(JSON.stringify((process.argv.length>2?process.argv.slice(2).map(Number):[64,317,1027]).map(runPerronCompensation),null,2));
