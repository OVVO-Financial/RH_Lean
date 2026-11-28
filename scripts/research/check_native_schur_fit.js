// Exact regression for the true-zero Schur fit on actual star layer amplitudes.
// No floating-point determinant, no substituted arithmetic row.
'use strict';
const assert = require('node:assert/strict');
const primes = [2,3,5,7,11,13,17,19,23,29,31,37];
const sum = a => a.reduce((s,x)=>s+x,0n);
const prod = a => a.reduce((s,x)=>s*x,1n);
const normal = D => D.map((_,i)=>prod(D.filter((_,j)=>j!==i)));
const dot = (a,b)=>sum(a.map((x,i)=>x*b[i]));
const mod = (a,p)=>(a%p+p)%p;
const unit = (a,p)=>mod(a,p)!==0n;
function det(M) {
  const A=M.map(r=>r.slice()), n=A.length;
  if(!n)return 1n;
  let den=1n, sign=1n;
  for(let k=0;k<n-1;k++){
    if(A[k][k]===0n){
      let j=k+1; while(j<n&&A[j][k]===0n)j++;
      if(j===n)return 0n;
      [A[k],A[j]]=[A[j],A[k]];sign=-sign;
    }
    const p=A[k][k];
    for(let i=k+1;i<n;i++)for(let j=k+1;j<n;j++){
      const a=p*A[i][j]-A[i][k]*A[k][j];
      assert.equal(a%den,0n); A[i][j]=a/den;
    }
    for(let i=k+1;i<n;i++)A[i][k]=0n;
    den=p;
  }
  return sign*A[n-1][n-1];
}
function amplitude(D,a){
  return D.map((v,i)=>[a[i],...D.slice(1).map((_,j)=>i===0?-D[0]:i===j+1?v:0n)]);
}
function gram(A,n){
  return A[0].map((_,i)=>A[0].map((_,j)=>sum(A.map((r,k)=>n[k]*r[i]*r[j]))));
}
function fit(D,E,n,p){
  const q=normal(D),r=normal(E),Q=sum(q),R=sum(r),d=D.length;
  const a=Array(d).fill(1n);
  const order=q.map((_,i)=>i).sort((i,j)=>{
    const x=q[i]*R+r[i]*Q,y=q[j]*R+r[j]*Q;
    return x<y?-1:x>y?1:i-j;
  });
  if(p===2n){
    if(d%2===0){
      const i=order.find(i=>unit(Q+q[i],p)&&unit(R+r[i],p));
      assert.notEqual(i,undefined);a[i]=2n;
    }
  } else if(!unit(Q,p)||!unit(R,p)){
    let chosen=false;
    for(const i of order){
      for(const k of [1n,2n])if(unit(Q+k*q[i],p)&&unit(R+k*r[i],p)){
        a[i]+=k;chosen=true;break;
      }
      if(chosen)break;
    }
    assert(chosen);
  }
  assert(unit(dot(q,a),p)&&unit(dot(r,a),p));
  const N=n.map(x=>unit(x,p)?x:x-1n);
  const w=()=>dot(N,a.map(x=>x*x));
  if(!unit(w(),p)){
    assert(p!==2n);
    const i=a.findIndex(x=>unit(x,p));
    const z=[n[i],n[i]-1n,n[i]-2n].find(x=>unit(x,p)&&unit(w()+(x-N[i])*a[i]*a[i],p));
    assert.notEqual(z,undefined);N[i]=z;
  }
  assert(unit(w(),p));
  assert(N.every((x,i)=>x>=n[i]-2n&&x<=n[i]&&unit(x,p)));
  const changes=a.map((x,i)=>x===1n?-1:i).filter(i=>i>=0);
  assert(changes.length<=1);
  if(changes.length){
    const i=changes[0],k=a[i]-1n;
    assert(d>1);
    assert(BigInt(d-1)*k*(q[i]*R+r[i]*Q)<=4n*Q*R);
  }
  return {a,N};
}
let state=123456789;
function rand(n){state=(Math.imul(state,1664525)+1013904223)>>>0;return state%n;}
let fits=0,determinants=0,losses=0,localSchur=0,repairs=0;
for(let d=1;d<=8;d++)for(let t=0;t<180;t++){
  const D=Array.from({length:d},(_,i)=>BigInt(primes[i])**BigInt(rand(5)));
  const E=D.map((_,i)=>BigInt(primes[i])**BigInt(rand(5)));
  const n=D.map(()=>BigInt(4+rand(120)));
  const q=normal(D),r=normal(E);
  // An exact partition into disjoint admission cells.
  const F=D.map((_,i)=>BigInt(primes[i])**BigInt(rand(3)));
  const groups=D.map(()=>rand(4));
  const A=Array(d).fill(1n),Q=dot(q,A),P=prod(F);
  let numer=1n,denom=1n;
  for(let g=0;g<4;g++){
    const f=F.map((v,i)=>groups[i]===g?v:1n),p=prod(f);
    numer*=sum(q.map((v,i)=>v*A[i]*(p/f[i])));denom*=Q*p;
  }
  const joint=sum(q.map((v,i)=>v*A[i]*(P/F[i])));
  assert(numer*Q*P>=joint*denom);
  assert(joint*F.reduce((a,b)=>a>b?a:b,1n)>=Q*P);
  losses++;
  for(const ell of primes){
    const p=BigInt(ell),{a,N}=fit(D,E,n,p);fits++;
    if(a.some(x=>x!==1n)||N.some((x,i)=>x!==n[i]))repairs++;
    for(const B of [D,E]){
      const b=normal(B),X=amplitude(B,a),H=gram(X,N),W=H[0][0];
      assert.equal(det(X),dot(b,a));determinants++;
      assert.equal(det(H),prod(N)*dot(b,a)**2n);determinants++;
      assert(unit(det(H),p));
      const S=H.slice(1).map((row,i)=>row.slice(1).map((v,j)=>W*v-H[0][i+1]*H[0][j+1]));
      const s=det(S);
      if(d===1)assert.equal(s,1n);
      else assert.equal(s,W**BigInt(d-2)*det(H));
      assert(unit(s,p));localSchur++;
    }
  }
}
console.log(JSON.stringify({fits,determinants,localSchur,losses,repairs}));