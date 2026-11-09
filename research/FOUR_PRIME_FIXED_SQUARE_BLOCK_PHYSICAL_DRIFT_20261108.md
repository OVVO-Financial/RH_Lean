# Fixed {2,3,5,7} square-clock attack: exact finite drift and mesoscopic return

**Status:** all finite arithmetic is independently certified by
`scripts/four_prime_fixed_squareblock_certificate.py`; the companion Lean module
formalizes the square-killing 44100-period mass and its exact infinite sparse
square-block drift, subject to exact-head warning-fatal CI. This is **not RH**
and is **not** a new Mertens exponent.

## One fixed coordinate set, three distinct fields

Hold the prime coordinates **exactly** at P={2,3,5,7}, W=210.

* Parity-only field `w4(n)=(-1)^#{p in P:p|n}`: period 210, zero period mean.
* Physical four-prime square-kill field `g4(n)`: sign flips on p|n and is zero
  if p^2|n for any p in P. It is **not** the ordinary Mobius function because
  primes >7 are still untouched. Its period is 44100.
* Ordinary `mu(n)`: all higher primes retain their **actual** sign and square
  masks; no additional prime is admitted into the fixed four-prime coordinate set.

The parity-only wheel has every-interval discrepancy <=13, hence
`|sum_{R^2<=n<(R+1)^2} w4(n)|<=13` for every R.

The 44100-period physical four-prime square-kill wheel has the **exact census**

`(+1,-1,0) = (14976,12672,16452)`, net `+2304`.
Thus `rho=2304/44100=64/1225>0`. Define
`G4(x)=sum_{1<=n<=x}g4(n)`. An exhaustive 44100-site rational certificate
gives for **every natural x**, by periodicity,

`-14364 <= 1225 G4(x)-64 x <=14428`.

Consequently for every root R,

`|1225*[G4((R+1)^2-1)-G4(R^2-1)] -64*(2R+1)| <=28792.`

At the infinite root family `R=44100*t` there is an **exact equality**

`sum_{R^2<=n<(R+1)^2}g4(n)=4608*t.`

This rules out O(1) or o(R) cancellation for the square-killing four-prime
**neutral-cofactor control model**, despite the perfect 210-parity balancing.
The actual square-killing block is strictly positive for every R>=103
(44,100-phase exhaustive certificate + `B4(R+44100)=B4(R)+4608`).
The last nonpositive control block is R=102.

The positive linear response also appears in the fully completed reciprocal
cube: `prod_{p in P}(1-1/p)=8/35>0`. Hence the unweighted identity
`sum_{d|210}mu(d)=0` **does not kill** coherent linear cofactor mass
`T(x)~c*x`: the weighted image is `(8/35)*c*x`.

## True Mobius cofactor decomposition: no lost primes

Let `S4(k)=sum_{d|210,d<=k}mu(d)`, `T(x)=sum_{n<=x,(n,210)=1}mu(n)`.
Then exactly

`M(x)=sum_{d|210}mu(d) T(floor(x/d))
     =sum_{m<=x,(m,210)=1}mu(m)S4(floor(x/m))`.

The finite `|S4|<=2` is sharp, and a completed orbit `210m<=x` vanishes.
Every cofactor m retains its full genuine Mobius sign.

For the original physical square-block sum write

`B_mu(R)=sum_{R^2<=n<(R+1)^2}mu(n)`,
`B_4(R)=sum_{R^2<=n<(R+1)^2}g4(n)`,
`D_4(R)=B_mu(R)-B_4(R)`.

The exact source-preserving identity is `B_mu(R)=B_4(R)+D_4(R)`.
No claim that `D_4(R)<=0` for every R is possible:
**R=137** is a literal counterexample, with `B_mu(137)=44`,
`B_4(137)=2`, `D_4(137)=+42`. Large-root numerical negativity of D4
is a finite observation, not a theorem.

## A genuine all-window signed HIGH compensation from the PAID strict OAI input

The latest strict source at merged PR #1116 establishes
`beta_*=7/8-5/(96*N_*)<1`, i.e. for every epsilon>0 there is a
cutoff-independent `C_epsilon` such that
`|M(x)|<=C_epsilon*x^(beta_*+epsilon)`.

For any integers H<=A<B<=2H, summing the exact source identity yields

`sum_{R=A}^{B-1} D_4(R)
  = - (64/1225)*(B^2-A^2)
    + O_epsilon(H^(2*beta_*+epsilon)+1)`.

Proof: telescope the actual M interval; subtract the **exact**
`G4(B^2-1)-G4(A^2-1)=(64/1225)(B^2-A^2)+O(28792/1225)`;
apply the already-proved source-faithful strict Mertens bound at both endpoints.

Thus for every fixed positive epsilon, on sufficiently large scales,
**every** root-window of length

`B-A >= H^(2*beta_*-1+epsilon)
     = H^(3/4-5/(48*N_*)+epsilon)`

has negative aggregate `D_4`, absorbing a fixed positive fraction of
the four-prime linear drift. This is an unconditional **mesoscopic**
cancellation theorem modulo the cited *already certified* strict OAI input;
it does not strengthen the Mertens exponent.

## Exact remaining mathematical seam

Prove a root-local or squared-energy **complete signed** strengthening of
the above root-window compensation, retaining actual rough-cofactor prime
parity. The four prime signs/square kills alone cannot provide it: the
strictly positive neutral-cofactor model satisfies those rules and is linear.

A valid new estimate must exploit actual rough-cofactor structure, including
inter-orbit covariance, and **cannot** insert a bound on D4 as a negative
credit with the wrong inequality direction. The first falsifier for proposed
pointwise signs is R=137. The four-prime kernel should remain fixed.

This packet refines the older parity-only
`RHLean/Arithmetic/FourPrimeWheelCancellation.lean` without identifying its
field with ordinary Mobius. It is not a repeat of the withdrawn tautological
roughness telescope as an independent power-saving theorem.
