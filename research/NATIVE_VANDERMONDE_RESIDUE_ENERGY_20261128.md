# Integral Vandermonde contradiction attack: positive residue energy

Actual consecutive slots 0,...,n-1, not synthetic signed populations.
The integer Vandermonde V_n=(i^j) has positive determinant
prod_{k=1}^{n-1} k^(n-k), by its difference product. The real logarithm
is pairLog n.

For d>=1 let q=floor(n/d), r=n mod d. There are r residue counts q+1
and d-r counts q; this follows by decomposing the actual interval into
q complete periods and its initial r slots. About their literal target
n/d the sum of squared deviations A_d=r(d-r)/d, nonnegative.
The number C_d of unordered slot pairs congruent mod d is
sum_{j=1}^q (n-jd)=qn-dq(q+1)/2. Counting ordered pairs also gives
2 C_d=sum_a count_a^2-n=n(n/d-1)+A_d. Thus

  2 log det V_n = n S(n)+sum_{d<=n} Lambda(d) A_d,
  T(n)=(1/n) sum_{d<=n} Lambda(d) A_d >= 0.

Here S is the original principal ramp, including prime powers.
No discarded complementary prime set. The arithmetic identity and
positivity are submitted in NativeVandermondeResidueEnergy.lean;
the actual occupancy interpretation and Vandermonde formula above
are paper-level, not new audited Lean declarations.

Independent archimedean size: sum_{k=1}^{n-1} log(k!) =
(n^2/2)log n-3n^2/4+O(n log n), by elementary Stirling and integral
comparison. Consequently
  (2/n) log det V_n=n log n-3n/2+O(log n),
  S(n)-M(n)=(gamma-1/2)n-T(n)+O(log n).
The original signed handoff at integer m=4 floor(x/4) now gives
  L_x+U_x=T(m)-(gamma-1/2)m
          +O(sqrt(x)log x+x^(eps/8)log x).
The required sufficient estimate is the single positive-statistic
lower bound
  T(m)>=(gamma-1/2)m-O_eps(m^(1/2+K eps)).
This still needs an independent proof on complete cofinal windows;
T>=0 alone only gives a linear error.

For w(t)=t{1/t}(1-{1/t}), 0<t<=1, T(n)=sum Lambda(d) w(d/n).
For Re s>1 integration by parts in u=1/t gives
  int_0^1 w(t)t^(s-1)dt=2 zeta(s)/(s(s+1))-1/(s(s-1)).
At s=1 the removable value is gamma-1/2; at every nontrivial zero
rho the value is 1/[rho(1-rho)]. Thus the positive kernel still
sees the actual RH obstruction, not just an easy zeta-null exchange.
The PNT supplies leading mass but not the desired quantitative lower bound.
The upper-half kernel integral is 3/4-log 2 (about 0.05685);
the full integral is about 0.07722.

Why the direct integral contradiction stalls: the consecutive slots
ALREADY minimize each modular sum of squared counts at fixed n,d.
Any rearrangement to distinct integer points can only raise the
collision energy. Its Vandermonde determinant also increases, by
the same prime-divisor accounting (including new larger differences).
Positivity/minimality of the determinant by itself cannot force
the missing weighted lower bound. The next meaningful attack is an
independent simultaneous lower bound on the weighted residue energy,
not claiming its nonnegativity is sufficient.

Exact regressions for n=1..256 and 1<=d<=n: 32,896 integer checks of
2d C_d=n^2-nd+r(d-r). Floating-point complete prime-power sum tests:
n=100: T=7.826773, baseline=7.721566;
n=1000: T=77.521146, baseline=77.215665;
n=10000: T=772.245024, baseline=772.156649;
n=100000: T=7719.732883, baseline=7721.566490;
n=1000000: T=77206.462340, baseline=77215.664902.
Strict nonnegativity of L+U is not a consequence; the deficit
relative to this positive energy baseline has both signs.
These tests do not prove the uniform inequality.

Upstream tether: compact Sernau 72fead102f663d5c7a407964a13dc0cf9d977207
Endgame/LongForms.lean:63-92 and New/Main.lean:121-145: an independent
lower estimate on the same object is the required source of contradiction.
No terminal theorem imported. RH remains open.
