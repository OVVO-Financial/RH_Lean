'use strict';
// Exact site-rank experiment, retaining physical multiplicity.
// Usage: node scripts/single_prime_site_recovery_20261125.js [Rmax=4096]
const Rmax=Number(process.argv[2]||4096),N=Rmax*Rmax-1;
if(!Number.isSafeInteger(N)||Rmax<128||Rmax>8192)throw Error('Choose integer Rmax in [128,8192]');
const primes=[2,3,5,7,11,13,17,19,23,29,31,37,41,43,47];
const owner=new Uint8Array(N+1);
for(const p of primes)for(let n=p;n<=N;n+=p)if(!owner[n])owner[n]=p;
const summary=()=>({blocks:0,nonzeroLayers:0,halfViolations:0,quarterViolations:0,thirdViolations:0,maxSigmaMin:0,peak:null,firstHalfFailure:null,firstQuarterFailure:null,nontrivialPairs:0,jointViolations:0});
const groups={all:summary(),p5:summary(),p13:summary(),p17:summary()},byPrime={};
for(const p of primes){
 const proper=new Set();for(let d=p*p;d<=N;d*=p)proper.add(d);
 const stat=summary();byPrime[p]=stat;
 const targets=[stat,groups.all,...(p>=5?[groups.p5]:[]),...(p>=13?[groups.p13]:[]),...(p>=17?[groups.p17]:[])];
 for(let r=p;r<Rmax;r++){
  const L=r*r,U=(r+1)*(r+1)-1;
  let d=0;const E=[];
  for(let n=L;n<=U;n++)if((owner[n]===0||owner[n]>=p)&&!proper.has(n)){
   d++;if(owner[n]===p){let q=n,k=0;while(q%p===0){E[k]=(E[k]||0)+1;q/=p;k++;}}
  }
  for(const s of targets)s.blocks++;
  for(let j=0;j<E.length;j++){
   const k=j+1,b=E[j];if(!b||!d)continue;
   const root=(b/d)**(1/k),w={p,r,k,b,d};
   for(const s of targets){
    s.nonzeroLayers++;
    if(BigInt(2)**BigInt(k)*BigInt(b)>BigInt(d)){s.halfViolations++;if(!s.firstHalfFailure)s.firstHalfFailure=w;}
    if(BigInt(3)**BigInt(k)*BigInt(b)>BigInt(d))s.thirdViolations++;
    if(BigInt(4)**BigInt(k)*BigInt(b)>BigInt(d)){s.quarterViolations++;if(!s.firstQuarterFailure)s.firstQuarterFailure=w;}
    if(root>s.maxSigmaMin){s.maxSigmaMin=root;s.peak=w;}
    for(let i=0;i<j;i++)if(E[i]){s.nontrivialPairs++;if(d*b>E[i]*b)s.jointViolations++;}
   }
  }
 }
}
console.log(JSON.stringify({Rmax,N,primes,groups,byPrime},null,2));
