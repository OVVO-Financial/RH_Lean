# Alpöge's map: signed-parent flow, exact collar saving, and the first genuinely nonlocal bill

**2026-11-21.** Experimental and formal algebra investigation attached to draft PR #1169.
Status: the pointwise positive-parent identities and midpoint ASK collar are
mathematical unconditional; **latest-head Lean compilation is pending**.
The explicit RH-strength one-sided finite-C inequality is NOT established.
The published external Alpöge final theorem and its kernel verification
do not constitute an independent native RH_Lean derivation.

## 1. New exact positive prime-parent transport

For n>=2 define mu_+(n)=max(mu(n),0), mu_-(n)=max(-mu(n),0),
and F(n)={p prime : p|n, p does NOT divide n/p}. In the real source:

    mu_+(n) = sum_(p in F(n)) (log p/log n)*mu_-(n/p)
    mu_-(n) = sum_(p in F(n)) (log p/log n)*mu_+(n/p).

For squarefree n>1, F(n) is the set of all prime factors,
and sum_(p|n) log p/log n=1. For nonsquarefree n, every fresh-prime
parent n/p is still nonsquarefree and both sides vanish. This is a
fully nonnegative Markov *row* normalization, with exact prime weights
and no independently assumed sign law.

Set X_R=R²-1, w_R(n)=1 for n<R, and -1 for R<=n<=X_R.
Define original two-wall positive populations

    U_R = mu_+(1) + sum_(2<=n<R) mu_+(n)
                   + sum_(R<=n<=X_R) mu_-(n),
    L_R = sum_(2<=n<R) mu_-(n)
                   + sum_(R<=n<=X_R) mu_+(n).

Inserting the identities above turns both U_R and L_R into nonnegative
weighted prime-parent sums. Exactly

    U_R-L_R = Q_R = 2M(R-1)-M(X_R),
    U_R+L_R = T_R = sum_(n<=X_R) mu(n)^2,
    4 U_R L_R = T_R²-Q_R².

Every coefficient is the original integer Mobius value, with the
strict history wall and top square wall retained.

Lean locations:
- `RHLean/Analysis/LogWeightedPrimeExtensionFiber.lean`, already on main:
  `moebiusReal_div_prime_eq_neg`, `sum_log_primeFactors_eq_log`,
  `not_squarefree_div_of_fresh_prime`.
- `RHLean/Analysis/AlpogePositivePrimeParentTransport.lean`, new in #1169:
  `alpogeFreshParentUPM_eq_muPlus`,
  `alpogeFreshParentLPM_eq_muMinus`,
  `alpogeFreshPrimeParent_probability_one`,
  `alpogeFreshTwoWallUPM_sub_LPM`.

## 2. Why the prime-parent averaging cannot be spent twice

This is an important source-exact constraint on a proposed shortcut, NOT a
logical obstruction to RH.

For every squarefree n, every fresh prime p|n has

    mu(n/p)=-mu(n).

Hence the entire *within-child* parent-sign variance is identically zero:

    sum_(p|n) log p * (mu(n/p)+mu(n))²=0.

For any completely multiplicative complex coefficient v (including
Alpöge's genuine Frobenius/inertia character coefficient `primVal_psi`
once its local idempotence is proved), the stronger identity is

    mu(n/p) v(n/p) v(p) = -mu(n) v(n),

including when v(p)=0 on a ramified family. Thus every parent of a fixed
child has the **same** returned twisted phase. Neither the number of
fresh prime factors nor orthogonality of the SAME child generates a
strict gain. A useful covariance must connect **different children,
distinct physical sites, or widths/heights** in Alpöge's partner map.

A second issue is column multiplicity: the n=1 parent has one fresh
prime child for every prime p<=X_R; its total outgoing incidence count
is pi(X_R), not O(1). For R=317 the exact count is 9,631, even though
each child has total incoming probability one. A row-stochastic
transition is not a bounded column operator by itself. It would be
incorrect to divide a global cost by the local number of prime parents.

## 3. New unconditional, quantitative genuine sharp-ASK collar saving

Let f_z(w)=max(z-w,0), b<=w_i<=B=b+eta and nonnegative weights
alpha_i summing to 1. With m=sum_i alpha_i*w_i,

    J(z) := sum_i alpha_i*f_z(w_i) - f_z(m).

By Jensen, J(z)>=0; since f_z is affine on both [b,z] and [z,B],
J(z)=0 when z<=b or B<=z. The convex-chord upper envelope gives

    0<=J(z)<=((z-b)*(B-z))/(B-b) <= eta/4

on b<z<B. This is sharp: equal weights at b,B and z=(b+B)/2
attain eta/4. The inequality remains exact with arbitrary positive
site weights **if m is the weight-dependent barycenter**.

Proof of the chord bound: for b<=w<=B and b<=z<=B,

    f_z(w) <= (z-b)*(B-w)/(B-b).

Average and subtract f_z(m). If m<=z, bound the gap by
`(m-b)*(B-z)/(B-b)`; if m>=z, bound it by
`(z-b)*(B-m)/(B-b)`. Each is at most
`(z-b)*(B-z)/(B-b)`.

Apply this to Alpöge's ACTUAL principal ASK with a>0, widths b,B,
and z=a/n, weighted by the original von Mangoldt (Lambda(n)>=0).
For two equally weighted widths, the Lean module
`RHLean/Analysis/AlpogeSharpASKCollar.lean` defines the exact gap and
proves

    0 <= PrincipalGap_N
      <= (B-b)/4 * sum_(2<=n<=N, b<a/n<B) Lambda(n).

This is a **prime-power** collar, not an unweighted integer interval
and not a substitute Dirichlet character. Its support is exactly

    a/B < n < a/b.

The general alpha-weighted Jensen bound is proved above on paper;
the new Lean module presently formalizes the *two-site midpoint*
and the full von-Mangoldt-weighted finite prime-power source.

For b>=1 and a/b=x with all relevant n<=x, the crude counting bound
`Lambda(n)<=log x` gives

    PrincipalGap_N <= (eta/4) * (x*eta/b+1)*log x.

This is size O((eta+x eta²/b)log x), substantially better than
charging a global Lipschitz eta times the entire psi(x) mass,
provided eta/b is small. At x=100,488, b=100, B=101,
direct von Mangoldt census gives

    actual midpoint gap J       = 118.2170523...
    collar Lambda mass           = 978.5791082...
    sharp upper collar bound     = 244.6447771...
    naive global Lipschitz      = 50250.3339919...,

a 425-fold smaller *observed actual cost* than the naive bound.
Finite numerical ratios are NOT asymptotic estimates.

## 4. How this intersects Alpöge's ORIGINAL geometry

In PR #1166 the full site-kernel prime-power coefficient is
`2/|I_p|` on the genuine inertia coset and ZERO elsewhere. This
is nonnegative on every prime power, even p=2,q,d, and correct
Frobenius/inertia orthogonality preserves the physical site.

For a **fixed prime-power** and fixed site, Jensen can apply to
variation over positive geometric-family widths. However, **unramified
prime powers have a singleton selected Frobenius site**: averaging
over distinct character colours at the same site gives no Jensen gain.
The full source involves site-dependent widths and nonprincipal modes.
The principal-component collar saving must therefore be combined with
the exact nonprincipal width/character return and the original
u0-averaging before being charged against `topExcess`.

The full paid geometry, partner map and cost from Alpöge are recorded
in `docs/RHLEAN_ALPOGE_FULL_COST_SEVEN_AGENTS_20261120.md` and
`research/ALPOGE_GZ_PHYSICAL_LIFT_ATTACK_20261120.md`.
The new collar theorem reduces ONE width-payment channel on a
source-exact physical carrier; it does **not** independently bound
the full ASK-MAIN error, the Mertens Q_R signed balance, or Gz.

## 5. Exact next quantitative proof objective

Reconstruct an all-family, all-character counterpart to the collar
with *complete* site-dependent mass:

    full ASK = principal ASK + three signed character ASK responses
             = sum_(physical site) nonnegative Frobenius/inertia
               prime-power masses times f_(a/n)(width_site).

Prove a normalizing *partner/width* double average, and bound the
difference between its arithmetic-weighted barycenters and the
geometric mean reference in MAIN. Retain the actual 2,q,d inertia
images, all prime-power powers, and all moving width/multiplicity
factors. Only then attempt a fixed-sign `Gz` estimate (or principal
`U_R-L_R` estimate) at R^(1+o(1)).

The special Euler/Liouville parity here is NOT an additive character
of a fixed finite host. Its between-child interaction is what the
nonlocal lift must pay.

**Acceptance:** a proof must show a net quantified saving on the
COMPLETE physical source after height/covolume and all complementary
signed terms. No separate local convexity or row-stochasticity
statement is promoted to RH without this payment.
