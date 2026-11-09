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


## Nested subwheel stress test: one prime already carries the entire Mobius problem

The fixed cancellation prime set need not be enlarged and may be reduced even
further. The exact 2/6/30/210 subwheel proof packet is
`research/FOUR_PRIME_SUBWHEEL_LOG_DIFFERENCES_20261108.lean`, checked by
`scripts/four_prime_subwheel_comparison.py`.

| selected coordinates P | W | physical period W^2 | signed mass / period | density rho_P | sharp max |S_P| | parity square-block max | last nonpositive physical block R |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| {2} | 2 | 4 | 1 | 1/4 | 1 | 1 | none |
| {2,3} | 6 | 36 | 4 | 1/9 | 1 | 1 | 9 |
| {2,3,5} | 30 | 900 | 64 | 16/225 | 2 | 7 | 39 |
| {2,3,5,7} | 210 | 44100 | 2304 | 64/1225 | 2 | 13 | 102 |

Each physical square-killing density is
`rho_P = product_{p in P} (1 - 1/p)^2 > 0`.
The exact infinite family at `R=W^2*t` has block mass
`2*t*(W^2*rho_P)`. The prime-2 model is **exactly**
`B_{g_2}(R)=ceil(R/2)` for all roots R.
Thus bounded square-block cancellation of the parity-only wheel holds already
for {2}, but it does not remain bounded once its p^2 square-kill condition is
restored. No finite P can use its sign/kill rules alone to force a sublinear
full-Mobius envelope.

The actual Mobius function nevertheless has **exact one-prime cancellation**:
`M(x)=sum_{x/2 < m <= x, m odd} mu(m)`. This follows by pairing every
odd m with 2m when 2m<=x; squareful m have mu=0 on both sides.
For every beta>0, the odd-rough sum and Mertens sum have the same admissible
O(x^beta) exponent, by the finite two-corner difference and its exact dyadic
inverse. This is an RH-equivalent reformulation, NOT a new estimate.

At the real square block R=137, `B_mu=+44` while the four neutral-cofactor
control block values are `69,30,22,2` respectively for W=2,6,30,210.
The last two corrections `B_mu-B_g` are **positive**, refuting any local
negative-correction assertion. The exact first one-prime correction is -25.

## What four coordinates genuinely buy: four orders of log-mode cancellation

On a log coordinate u, define `D_h f(u) = f(u)-f(u-h)`.
The finite prime Euler operator is
`D_{log 7} D_{log 5} D_{log 3} D_{log 2}`.
Its exact polynomial cancellations are:

* one shift kills constants and sends `u` to `h2`;
* two shifts kill degree <2 and send `u^2` to `2*h2*h3`;
* three shifts kill degree <3 and send `u^3` to `6*h2*h3*h5`;
* four shifts kill degree <4 and send `u^4` to `24*h2*h3*h5*h7`.

These are Lean statements for arbitrary real shifts h, so logarithmic
specialization needs no additional analytic theorem. This is a genuine
distinction among 1,2,3,4 fixed prime coordinates: four primes kill cubic
smooth-log principal profiles, while one kills only constants.

**However**, a positive-power mode `x^beta`, beta>0, survives with
the *nonzero* factor `product_{p in P}(1-p^(-beta))`.
So the log-cancellation order alone cannot improve a Mertens exponent.
The remaining signed rough cofactor source and physical clipping must still
be estimated jointly. Do not confuse the nonzero scalar power-mode multiplier
with a verified operator contraction on the full original Mertens source.


## 2026-11-08: CRITICAL CORRECTION — operate only below the square root

The true frozen-history theorem must **not** be replaced by the post-root
identity `M(X)=sum_{X/2<m<=X,m odd} mu(m)`; that expression introduces
unknown post-root cofactor values. Instead set `X=R^2-1` and use only
`mu(a)` for `1<=a<R`:

```text
Q_R := sum_{a,b < R, a,b >=1} mu(a)*mu(b)*floor(X/(a*b)).
M(X) = 2*M(R-1) - Q_R.
```

The strengthened **pointwise** form is

```text
c_R(n) := sum_{1<=a,b<R; a*b | n} mu(a)*mu(b)
c_R(n) = mu(n)   for 1<=n<R;
c_R(n) = -mu(n)  for R<=n<R^2.
```

Proof: write `Z_R(s)=sum_{n<R}mu(n)n^-s`,
`T_R(s)=sum_{n>=R}mu(n)n^-s`. The Dirichlet-series identity
`zeta*Z_R^2 = muSeries - 2*T_R + zeta*T_R^2` is coefficientwise valid
formally, and `T_R^2` has zero coefficients at every `n<R^2`.
This is **exact reconstruction**, not an estimate and not a prime-count
hypothesis. The square-block source follows by subtracting consecutive R:
`B_R = 2*mu(R) - (Q_(R+1)-Q_R)`.

### Prime-two exact reduction within the *historical* sum

For each odd `m<R` define `h_R(m)=1` if `2m<R`, else 0.
Mobius square-killing and the 2-flip give

```text
Q_R = sum_{odd 1<=m,n<R} mu(m)*mu(n)*H_R(m,n)
H_R(m,n)=floor(X/(mn))
         -(h_R(m)+h_R(n))*floor(X/(2mn))
         +h_R(m)h_R(n)*floor(X/(4mn)).
```

No `mu` at index `>=R` appears. The *historical* first-corner
completion region is `m<R/2` for {2}; for {2,3,5,7} it is only
`m<R/210`. Therefore the smaller fixed prime set genuinely expands
the fully admitted root-carrier range; earlier whole-period toy-model
tests did not capture this advantage.

Split odd parents into L=`2m<R`, H=`2m>=R`.
For `m,n in H`, `1<=floor(X/(mn))<=3`, so

```text
Q_R(H,H) = M(R-1)^2 + H2_R + H3_R
Hq_R = sum_{m,n in H, mn<=floor(X/q)} mu(m)*mu(n), q=2,3.
```

The constant term is exactly the *historical* square because
`sum_{m in H}mu(m) = M(R-1)`, using only the prime-two pairing at
`R-1`. This separates the root-adjacent High-High source into one
already-paid square and precisely **two signed hyperbola masks**.
For clarity the full root kernel is

`Q_R = Q_LL(R) + Q_LH(R) + M(R-1)^2 + H2_R + H3_R`

where `Q_LH` contains both orientation orders and all terms use
`mu(m),mu(n)` with `m,n<R`.

Combining the exact bridge gives

```text
M(R^2-1)-1 = -(M(R-1)-1)^2
             -(Q_LL+Q_LH+H2_R+H3_R).
```

The **genuinely OPEN** source-faithful finite-A theorem is one
unconditional fixed `C` such that the absolute value of the right side
is at most `C*R*sqrt(K_R)` for every R>=2, where
`K_R=max_{0<=y<R}(M(y)-1)^2/(y+1)>=1`.
No sign or separate absolute-value estimate on H2/H3 is substituted for
the complete signed sum. This is exactly the already Lean-certified
finite-A => RH consumer, not a proposed changed criterion.

### Independently computed finite census from only the frozen mu prefix

The C++ certificate `frozen_root_two_coordinate_census.cpp` is
available in the chat artifact and reproduces the following arithmetic:

| R | Q_LL | Q_LH (both orientations) | M(R-1)^2 | H2 | H3 | Q_R | M(R^2-1) |
|---:|---:|---:|---:|---:|---:|---:|---:|
|317|29|-32|9|4|12|22|-28|
|1027|-179|-70|16|-73|-69|-375|367|
|5561|484|1106|25|462|477|2554|-2544|
|10000|654|-2314|529|-831|-12|-1974|1928|

No Mobius coefficients above R-1, no pi(x) estimate, and no zeta-zero
assumption are used in this reconstruction. The numerical table is a
finite test, not a universal bound. These new general exact identities
are paper-level in this packet until added to the Lean theorem DAG.

**Research direction:** invoke the existing unique first-owner
triangular rank-drop, completed four-corner, same-branch and signed
polarization results on the **root-truncated odd-parent** kernel.
Target one complete signed `Q_LL+Q_LH+H2+H3` estimate with the
historical square retained; do not re-introduce post-root Mobius values.
