# #919: OAI to native Sector Six — the exact owner-two signed-moment target

Status: October 9, 2026. This is an **actual-prime arithmetic reduction** and an
exactly reproducible finite signed-flux probe. The native Lean theorems are in
VF_MID_919_OAI_OWNER_TWO_SIGNED_BOUNDARY.lean; the script is
scripts/vf_919_owner_two_signed_boundary_probe.py. The uniform mixed moment
needed for an RH-scale improvement is **NOT PROVED** here.

## 1. Do not start from an arbitrary character-row gram

On native first-owner cell p=2 and lower-prime signature empty, put

\[
 X_R=R^2-1,\quad C_R=M(X_R),\qquad
 J_R=\sum_{\substack{1\le a\le \lfloor X_R/2\rfloor\\2\nmid a}}
    \mu(a)\,w_R(2a).
\]

The site weight is the EXISTING compiled AMP common-clock weight,

\[
 w_R(n)=1_{\{n\ge R\}}+
 \sum_{\substack{q\ {\rm odd\ prime}\\q^2<R}}
  \frac1q\,1_{\{n\le\lfloor X_R/q^2\rfloor\}}.
\]

The exact native signed boundary is

\[
 \boxed{B_R=-2C_RJ_R=-2M(X_R)J_R.}\tag{B1}
\]

C_R=M(X_R) is ALREADY kernel-proved by
lowOwnerFirstOwnerClippedAmplitude_two_eq_topMertens. The new #919
vf919OwnerTwoSignedBoundary_eq_topMertens_times_returned kernel theorem
attaches it to the ACTUAL returned-parent amplitude, not a surrogate.
vf919OwnerTwoSignedGram_eq_interior_sub_branches_add_boundary retains B_R
with BOTH original branch squares before estimation.

This is the precise 1-dimensional terminal inlet of the compensated
full-cell telescope. It is NOT by itself the whole historically charged
Sector Six payment; no such equivalence is claimed.

## 2. Exact closed arithmetic formula for the returned child

Let O(y)=sum_{1<=n<=y, n odd} mu(n). It is a genuine Mobius prefix,
not a fantasy series.

Fubini on the actual site weight (using 2a <= X_R for admitted parents)
gives the exact finite identity

\[
 \boxed{
 J_R=
 O(\lfloor X_R/2\rfloor)
 -O(\lfloor (R-1)/2\rfloor)
 +\sum_{\substack{q\ {\rm odd\ prime}\\q^2<R}}
     \frac1q\,O\bigl(\lfloor X_R/(2q^2)\rfloor\bigr).
 }\tag{B2}
\]

Because mu(2a)=-mu(a) for odd a and mu(4a)=0,

\[
 M(y)=O(y)-O(\lfloor y/2\rfloor),\qquad
 \boxed{O(y)=\sum_{j\ge0}M(\lfloor y/2^j\rfloor).}\tag{B3}
\]

The second sum is finite (stop as soon as the cutoff reaches zero). Thus
B1–B3 express the entire native signed clipped/returned boundary as an
explicit *two-scale Mertens correlation*, with exact q-squared daughter
cutoffs and reciprocal 1/q weights.

No independent owner estimate, skipped negative source, or missing
clipped-square payment is hidden. The numerical script checks B1–B3
against the independently reconstructed physical a-sites, at six
roots including 317 and 1027.

### Why this is a sharper OAI extraction target

OpenAI's September 30 manuscript gives zeta and Dirichlet-L nonvanishing
for Re(s)>7/8. The natural analytic input to B1–B3 is therefore
the reciprocal zeta 1/zeta(s), *at the trivial character row itself*,
not an arbitrary attempt to match the Hecke c*n^3 coefficient term by term
with squarefree integers.

For Re(s)>1, Dirichlet series give exact identities

\[
 \sum_{n\ge1}\frac{\mu(n)}{n^s}=\frac1{\zeta(s)},\qquad
 \sum_{\substack{n\ge1\\n\ {\rm odd}}}\frac{\mu(n)}{n^s}
   =\frac1{(1-2^{-s})\zeta(s)}.
 \tag{B4}
\]

Perron inversion, with nonintegral cutoffs and the usual justified
limits, therefore gives a **two-variable** reciprocal-zeta representation
for B_R. More explicitly, put x=X_R+1/2 and y=R-1/2.
The second Mellin kernel is

\[
 \mathcal K_R(t)=2^{-t}
   \left[x^t\left(1+\sum_{q^2<R,\ q\ {\rm odd\ prime}}
     q^{-1-2t}\right)-y^t\right].
 \tag{B5}
\]

On initial lines Re(s)=Re(t)>1, in the sense of the iterated Perron limits,

\[
 \boxed{
 B_R=-2\,\operatorname{Perron}_{s,t}
 \frac{x^s\,\mathcal K_R(t)}
 {s\,t\,\zeta(s)\zeta(t)(1-2^{-t})}.}
 \tag{B6}
\]

CAUTION: B6 is an analytic reformulation, NOT an additional kernel-checked
Lean theorem. Discontinuity conventions, tails, and limit interchanges
must be proved before using it in a contour estimate. In particular, a
bound on one reciprocal zeta factor must not be mistaken for a bound on
the **signed, two-variable cross correlation** in B6.

This clean zero-frequency problem is the most direct place to try to
adapt OAI's inverse-character moments: work with a completed version
of the entire B6 kernel, before Cauchy and before splitting C and J
into positive energies.

## 2b. The missing Hecke-to-rational arithmetic coefficients have an EXACT dictionary

There is a more precise entry point than trying to identify OpenAI's
completed c*n^3 coefficients with individual ordinary squarefree integers.

For F=Q(sqrt(-3)), let mu_F(ideal) be the ideal Möbius function and define

\[
 a_F(n)=\sum_{N\mathfrak a=n}\mu_F(\mathfrak a),\qquad
 \chi_{-3}(n)=
 \begin{cases}0&3\mid n\\1&n\equiv1\pmod3\\-1&n\equiv2\pmod3.\end{cases}
\]

The classical exact Dedekind factorization and Dirichlet convolution give

\[
 \zeta_F(s)=\zeta(s)L(s,\chi_{-3}),\qquad
 \boxed{\mu(n)=\sum_{d\mid n}\chi_{-3}(d)a_F(n/d).}\tag{B9}
\]

It is a **coefficientwise equality of arithmetic functions**, not merely
equality of complex phases. In particular, it preserves split/inert
multiplicities instead of falsely identifying one ideal with one integer:

| Rational prime | Norm-ideal coefficient a_F(p) | chi_{-3}(p) | rational mu(p) |
|---|---:|---:|---:|
| 2 (inert) | 0 | -1 | -1 |
| 3 (ramified) | -1 | 0 | -1 |
| 7 (split) | -2 | +1 | -1 |

For p=2, a_F(4)=-1 while chi_{-3}(4)=+1, giving
mu(4)=a_F(4)+chi_{-3}(2)a_F(2)+chi_{-3}(4)=0,
exactly as required.

**New mathematical/Lean entrypoint:**
VF_MID_919_OAI_QUADRATIC_NORM_EULER.lean formally proves the
polynomial local identity, for every prime-residue case,

\[
  E_{F,p}(t)=(1-t)(1-\chi_{-3}(p)t),
  \quad E_{F,p}\in\{(1-t)^2,\,1-t^2,\,1-t\},
 \tag{B10}
\]

and its product over an arbitrary finite prime-label set. That is the
correct local multiplicity/zero-factor dictionary. The Lean module
does **not** independently prove algebraic number-field prime splitting
or the global identity B9; the analytic number-field interpretation of
its Euler factors remains to be imported/verified.

On finite cutoffs B9 yields the exact formula

\[
 \boxed{M(X)=\sum_{d\le X}\chi_{-3}(d)
                \sum_{N\mathfrak a\le X/d}\mu_F(\mathfrak a).}
 \tag{B11}
\]

This is the concrete coefficient-level bridge from the OAI's IDEAL
Mobius input to VF's ACTUAL rational Mertens clipped boundary. But
it also identifies a missing **quadratic-character cross-convolution**:
the d sum carries signs, and applying absolute values to the inner
ideal Möbius sums destroys their cancellation. One cannot use
the Dirichlet-convolution formula to infer a rational power saving by
termwise bounds on a_F.

### Correction: OAI Sixth-power amplification DOES save the principal ideal row

The previous paragraph, which concluded that **no published OAI moment provides a
principal-row saving**, was incorrect. It analyzed only the MARKED inverse
moment (old-eq:4.1) and omitted the separate **Sixth-power amplification**
lemma, `lem:inverse-amplification` / `eq:amplified-note`, in OpenAI's
September 30 manuscript (paper.tex, near lines 12362–12455).

For a fixed permitted annular smooth test W, fixed character presentation nu,
the original zero extensions, and **zero prime slots**, define

\[
 M_u(D;W)=D^{-1/2}\sum_{\mathfrak n}
     \mu_F(\mathfrak n)\nu(\mathfrak n)
     \chi_{\mathfrak n}(u)^{\varepsilon_\chi}
     W(N\mathfrak n/D).
\]

OAI proves, for any fixed c>0,

\[
 \sum_{N u\asymp U}|M_u(D;W)|^2
 \ll_{c,\epsilon,W,\mathrm{fixed\ data}}
 \max\{U,\;U^{1/6}D^{5(1+c)/6}\}(UD)^\epsilon
\tag{B12}
\]

over sixth-power-free element rows with all the original fixed exclusions.
**The row u=1 is included** (take U=1), so choosing c sufficiently
small in terms of epsilon and absorbing bounded initial D gives

\[
 \boxed{|M_1(D;W)|^2\ll_\epsilon D^{5/6+\epsilon},}
 \qquad
 \boxed{\left|\sum_{\mathfrak n}\mu_F(\mathfrak n)
           \nu(\mathfrak n)W(N\mathfrak n/D)\right|
           \ll_\epsilon D^{11/12+\epsilon}.}
 \tag{B13}
\]

This is an **actual, unconditional, principal-row ideal-Mobius
power saving in OAI's fixed smooth/masked setting**. It uses averaging
over auxiliary SIXTH-POWER multiples of the row and does not follow from
the original unamplified marked lemma. The precise arithmetic presentation,
annular seminorms, excluded prime support S and uniformity conditions in the
lemma must be retained.

Why it does **not** pay the native signed clipped boundary:

1. The available B13 sum is over ideals, includes nu and the OAI fixed
   zero extensions, and uses a fixed smooth annular weight. The native
   C_R=M(R^2-1) has a SHARP rational-integer cutoff and all Euler factors,
   especially p=2. Excluded Euler factors and a smoothing/Perron
   completion with controlled unsmoothed tails are still necessary.
2. Rational Mobius is the exact convolution B9:
   `mu_Z = chi_{-3} * a_F`. Even a sharp ideal-Mobius
   O(D^{11/12+epsilon}) estimate cannot be inserted through B11 termwise
   without losing the saving to the growing quadratic-character
   convolution. The signed d-sum needs to remain intact.
3. The boundary is B1 = -2 M(X_R) J_R with J_R the **different**
   q²-daughter-weighted odd-Mobius return B2. Bounding M and J
   independently sacrifices the cross-correlation whose sign is needed.
   The complete B6 numerator and BOTH negative native branch squares
   must remain together.
4. The exponent 11/12 > 7/8. Even an ideal sharp-cutoff saving of
   11/12 would not strengthen the best claimed zeta line 7/8, still less
   give the RH-scale R² boundary payment.

**The next analytic target is now more precise:** transfer the
sixth-power amplification mechanism to a **uniform signed cross
estimate for the COMPLETE B6 two-factor expression**, with the
quadratic convolution, deleted prime Euler factors, moving q²
daughter kernel, and justified sharp-cutoff limit. Feed the resulting
bound into the **full native signed telescope**

\[
 2G_R=I_R^2-L_R^2-J_R^2-2C_RJ_R,
\]

without replacing `-L_R²-J_R²` by zero or spending only an
unsigned bound on C_R or J_R. The remaining stage must also identify
the historical Sector Six first-bad source with this signed ledger.
This stronger B6 estimate and historical identification are **open**.
B12 and B13 are sourced statements of the external manuscript, NOT
new RH_Lean kernel-certified imports.


## 3. What the OAI 7/8 result ALREADY offers, and what it does not

With a standard quantitative zero-free-to-Mertens theorem (not imported
into the pinned RHLean kernel), the OAI 7/8 zeta nonvanishing would give,
for every epsilon>0,

\[
 |M(y)|\le A_\epsilon (y+1)^{7/8+\epsilon}.
\]

Write theta=7/8+epsilon>0, and assume for clarity
|M(y)|<=A y^theta for all integers y>=1 (absorbing the finite initial
range into A). From B3 and geometric summation,

\[
 |O(y)|\le \frac{A\,y^\theta}{1-2^{-\theta}}.
\]

Putting this in the EXACT B2 gives the fully explicit finite-power
bound

\[
 \begin{aligned}
 |J_R|\le
  \frac{A\,2^{-\theta}}{1-2^{-\theta}}\Big[
  X_R^\theta+(R-1)^\theta+
  X_R^\theta\sum_{q^2<R,\ q\ {\rm odd\ prime}}
                   q^{-1-2\theta}\Big].
 \end{aligned}\tag{B7}
\]

Therefore B1 yields the absolute estimate
\[
 |B_R|=O_{\epsilon}(R^{7/2+4\epsilon}).\tag{B8}
\]

This is a **concrete transfer** of OAI-style cancellation information to
the very native clipped/signed boundary the repo actually uses. But the
exponent 7/2 is too large for an R^2-scale boundary budget; even the
stronger 7/8 analytic half-plane does not by itself provide a gain in
the joint Mertens correlation. One must not claim otherwise.

The genuinely new desired input is instead a **signed** (not absolute
factor-by-factor) contour/row-moment estimate for the WHOLE B6 kernel,
strong enough to budget B_R at the actual return-envelope scale, and a
second exact comparison to the historical Sector Six source. This is
the specifically missing *two-factor* inequality, not another C-to-R map.

## 4. Direct finite numerical evidence and sign obstruction

Reproduce with:

    python3 -B scripts/vf_919_owner_two_signed_boundary_probe.py 1600

The script constructs exact genuine mu(n) for n <= Rmax^2-1;
checks the dyadic odd-Mertens identity B3; evaluates B2; then
**independently** enumerates literal AMP admitted parent a-sites using
w_R(2a) and enumerates clipped p-free sites. All six direct checks pass.

Sample values:

| root R | C=M(R^2-1) | J returned | -2CJ | (-2CJ)/R^2 |
|---:|---:|---:|---:|---:|
| 8 | -1 | -7 | -14 | -0.218750 |
| 17 | -7 | -8 | -112 | -0.387543 |
| 56 | 6 | -19.600000 | +235.200000 | +0.075000 |
| 119 | 14 | -39.152381 | +1096.266667 | +0.077415 |
| 317 | -28 | -18.907348 | -1058.811463 | -0.010537 |
| 1027 | 367 | -200.946925 | +147495.043093 | +0.139842 |
| 1600 | 360 | -189.343627 | +136327.411115 | +0.053253 |

On every integer root 8<=R<=1600, **positive B_R occurs 1,133
times**, negative 447, zero 13. Positive B_R cannot be discarded as
nonpositive "automatically compensated mass": its actual signs are
frequently dangerous! The signed sum of B_R across these roots is
+38,371,091.6183, an observed finite statistic NOT an all-scale law.

This directly identifies the term whose sign/cancellation OAI methods
must ultimately certify. A rowwise norm estimate erases precisely
the sign distinction that matters.

### Complete signed telescope: negative branch squares are NOT discarded

The latest finite probe also verifies, by an **independent direct enumeration**
of the actual admitted parent sites, both
\[
L_R=O(\lfloor X_R/2\rfloor)-O(R-1)
   +\sum_{q^2<R,\,q\text{ odd prime}}\frac1q\,
       O(\lfloor X_R/q^2\rfloor),
\qquad
I_R=L_R-J_R=Q_R-M(R-1),
\]
and, on every sampled root, the full first-owner identity
\[
\boxed{2G_R=I_R^2-L_R^2-J_R^2+B_R
             =-2(L_R+C_R)J_R.}\tag{B14}
\]
The `-L_R²` and `-J_R²` payments are now **kept in the numerical
report**, not estimated away.

| R | clipped signed B_R | negative branches -L²-J² | full 2G | full 2G/R² |
|---:|---:|---:|---:|---:|
| 56 | +235.200 | -682.627 | -442.027 | -0.140952 |
| 119 | +1096.267 | -2849.562 | -1745.078 | -0.123231 |
| 317 | -1058.811 | -689.296 | -1747.629 | -0.017391 |
| 548 | +43183.572 | -17393.991 | +25793.423 | +0.085891 |
| 1027 | +147495.043 | -71449.689 | +76654.457 | +0.072677 |
| 1600 | +136327.411 | -61537.131 | +75635.619 | +0.029545 |

For every root 8<=R<=1600 in this *finite* census the maximum
positive `2G_R/R²` is approximately **0.085891 at R=548**,
whereas the clipped term alone has maximum positive `B_R/R²`
approximately **0.287332 at R=57**. These are NOT all-scale estimates
and say nothing by themselves about the full historical Sector Six.

**Implication for the OAI attack:** Seek a signed power saving on the
complete B6-derived mixed boundary **inside B14**, with the two
negative branches retained. Proving only a bound on the individual
amplified principal row, or only on |B_R|, does not realize this payment.


## 5. Critical source compatibility

The OpenAI paper's selected-prime slot sets explicitly exclude its
fixed S, including all primes over 2 and 3. The VF owner-two anchor
therefore **cannot** be identified with one of OAI's marked selected
primes. Use OAI's *global reciprocal L-functions and completed inverse
moments* to inform B6 instead, or prove an exact stage of its Poisson
assembly that carries these excluded local factors into B6.

OpenAI also allows completed ideals A=c*n^3 with cubic powers.
The B4 principal Mobius series is only the squarefree zero-frequency
projection, NOT a coefficientwise equality with that completed Hecke
sum. Do not discard the higher valuations by declaration.

The native phase-aligned full cell is already proved in
VF_MID_919_OAI_PHASE_ALIGNED_OWNER_COMPENSATION.lean. That module gives
both signed -2Re(C conj(J)) and all phases at a general first owner p.
At the physical trivial-character p=2 cell it reduces to B1.

### Next quantitative route

Prove a *uniform signed two-variable reciprocal-zeta/Hecke moment*
for the completed kernel B6, uniformly in R and in smooth cutoff
parameters, BEFORE applying absolute values separately to the two
reciprocal factors. Then attach the result to the existing historical
Sector Six source with survivor restrictions, owner ages, and
once-charged negative returns retained. The first part is a new
analytic theorem; the second part is an actual-source dictionary.

No such two-variable saving, RH bound, or whole-Sector-Six payment is
claimed in #919.

## 6. New fixed-smooth complete-AMP transfer: OAI amplification to R^(11/3+eps)
**Scope:** This subsection proves the analytic deduction *conditional on the
published OpenAI sixth-power amplification lemma* at the principal element
row and on the standard Dedekind-zeta Euler coefficient dictionary.  This is
NOT an independently kernel-proved import of the OAI lemma.  The accompanying
Mathlib-only finite-width **sharp-recovery algebra** is kernel checked in
`VF_MID_919_OAI_SHARP_SMOOTH_NO_GAP.lean`; that algebra does not control
smooth seminorm constants.

Write `X_R=R^2-1`, `x=X_R+1/2=R^2-1/2`, and
`y=R-1/2`. For any **fixed** smooth compactly supported
`V:[0,infinity)->R` which is 1 near zero, define

```text
M_V(T) = sum_{n>=1} mu(n) V(n/T)
A_(R,V) = M_V(x) - M_V(y)
          + sum_{q odd prime, q^2<R} (1/q) M_V(x/q^2).
```

For `chi=chi_{-3}` and the norm-grouped ideal-Mobius coefficient
`a_F(n)=sum_{Norm ideal=n} mu_F(ideal)`, the exact Dirichlet
convolution `mu_Z=chi * a_F` is B9. Set
`C_chi(t)=sum_{d<=t}chi(d)`, so `|C_chi(t)|<=1` for all real t,
and `W(u)=u*V'(u)`, a **fixed annular** smooth test. Abel summation
of the quadratic-character variable, followed by ordinary Fubini
(the sums are finite on the support), yields the exact identity

```text
M_V(T) = - integral_{1}^{infinity} (C_chi(t)/t) J_W(T/t) dt,
J_W(D) = sum_{ideal a} mu_F(a) W(Norm(a)/D).
```

OpenAI's published lemma `lem:inverse-amplification` /
`eq:amplified-note` specializes to the principal sixth-power-free
element row `u=1`, fixed trivial `nu`, and zero marked prime slots.
Its normalized principal ideal sum then obeys
`|D^(-1/2) J_W(D)|^2 << D^(5/6+eps)`, hence

```text
|J_W(D)| <<_{W,delta,S} D^alpha,
alpha = 11/12 + delta.
```

To use the *unrestricted* ideal sum, restore the finitely many fixed
excluded prime-ideal Euler factors: each contributes a finite
squarefree-divisor sum of rescaled tests. Their total cost is a
fixed constant independent of D. For bounded positive D the
annular ideal sum is bounded directly, so the same exponent can be
used in the whole Abel integral. Thus

```text
|M_V(T)| <<_{V,delta} T^alpha
  * integral_1^infinity t^(-1-alpha) dt
 <<_{V,delta} T^alpha.
```

It follows directly from the **complete** smooth AMP expression that

```text
|A_(R,V)| <<_{V,delta}
  x^alpha (1 + sum_{q odd prime} q^(-1-2*alpha))
  + y^alpha
 <<_{V,delta} R^(2*alpha);
|A_(R,V)|^2 <<_{V,eps} R^(11/3+eps).
```

Here the quadratic-character summatory cancellation **is genuinely
used**, with no exponent lost to the growing `chi * a_F` convolution.
Nevertheless, the *last* bound uses the triangle inequality among the
`x`, `y`, and q^2 daughter components; it does **not** retain the
cross-component signed covariance required for the RH-scale Sector Six
payment. For comparison, a separate quantitative 7/8 zero-free-to-Mertens
transfer would give a stronger exponent `R^(7/2+eps)` for the square,
but likewise not the RH-scale `R^2 K` bound.

### Exact finite-width sharp recovery (no limiting interchanges)

A key refinement is that the midpoint offsets make all sharp sites
**arithmetically separated** from the smoothing transition. Let
`V_h(u)=1` for `u<=1-h` and `V_h(u)=0` for `u>=1+h`,
with `0<h<1/(2x)`. Because `n*q^2` and `X_R`
are integers,

```text
V_h( n*q^2/x ) = 1_{n*q^2 <= X_R},   for EVERY integer n,q.
V_h( n/y )     = 1_{n <= R-1}.
```

The first identity also covers `q=1`. Therefore at every fixed
root `R>=2` the **whole** physical AMP amplitude is recovered
exactly from this ONE smooth window:

```text
A_(R,V_h)
  = M(X_R) - M(R-1)
    + sum_{q odd prime, q^2<R} (1/q) M(floor(X_R/q^2))
  = lowOwnerZeroFrequencyMobiusAmplitude R.
```

The individual no-gap assertions are formalized by
`vf919HalfIntegerWindow_eq_sharp`,
`vf919SquareQ2Window_eq_sharp`, and
`vf919RootWindow_eq_sharp`. This avoids the need to argue about
pointwise convergence at a discontinuous endpoint or to exchange an
unspecified smoothing limit with an infinite sum. It DOES NOT avoid
the uniformity problem: `h` necessarily shrinks on the order
`R^(-2)`, and the derivatives of `W_h(u)=u V_h'(u)`
typically grow like `h^(-k-1)=R^(2k+2)`.

The published OAI lemma gives constants dependent on finitely many
smooth seminorms, not a root-uniform estimate at these shrinking windows.
Even a hypothetical seminorm-uniform `11/12` bound would leave
`R^(11/3+eps)`, well above the necessary `R^2 K` budget.

**Actual next quantitative target:** Obtain an estimate for the
*whole* signed returned-core integrand

```text
J_W(x/t) - J_W(y/t)
 + sum_{q odd prime, q^2<R} (1/q) J_W(x/(q^2*t))
```

*before* triangle inequality, uniformly for the root-dependent
`W_h`, and retain the negative branch squares in the complete
native telescope. The remaining arithmetic/analytic gain must be
stronger than what the published scalar sixth-power amplification
provides. No new zero-free exponent or RH claim follows from this
section.


## 7. Seminorm-free recovery takes place AFTER the character Abel integral

**Correction to the attempted pointwise amplification:** for a shrinking
window, no estimate of `J_{W_h}(D)` uniform in the smooth seminorms can
hold, even near fixed D=3. If `V_h(1-h)=1`, `V_h(1+h)=0`, the mean
value theorem gives a point `u_h` with
`V_h'(u_h)=-1/(2h)`. Its profile `W_h(u)=u V_h'(u)`
has `W_h(u_h)=-u_h/(2h)`. With `D_h=3/u_h`,
`h<1/7` and the excluded Euler factors restored, the unique ideal
of norm 3 contributes `J_{W_h}(D_h)=u_h/(2h)`.
For `R>=4`, at `t_h=x*u_h/3`, the other AMP
root/daughter scales are absent, so the full
`mathcal J_R(t_h)` has this arbitrarily large spike.
This is an obstruction to a POINTWISE uniform bound, not an
obstruction to the SIGNED INTEGRATED target.

There is a direct and substantially stronger exact recovery identity
*inside the integral*. Write `T=N+1/2` for any integer `N>=0`
and choose `0<h` with `h*T<1/2`. For any positive
integer norm `m`, and for **every** `u in [1-h,1+h]`,
the half-integer gap proves

```text
       d*m <= T*u   iff   d*m <= N     (all integer d>=1).
```

In particular the truncated quadratic-character prefix
`C_chi(T*u/m) = sum_{d*m<=N} chi(d)` is **constant on the
entire window**, not merely at `u=1`.
For a differentiable `V_h` transitioning from one to zero with
`V_h'` supported in this window, `W_h(u)=u V_h'(u)` and
the substitution `u=m*t/T` give the finite, exact identity

```text
- integral_{t=1}^infinity C_chi(t)/t * W_h(m*t/T) dt
  = - integral_{u=m/T}^infinity C_chi(T*u/m) * V_h'(u) du
  = sum_{d*m<=N} chi(d).
```

For `m<=N` the transition lies wholly above `t=1`; for
`m>N` the transition lies wholly below `t=1` and contributes
zero. Thus the formula holds for **all positive integer norms**.
The O(1/h) derivative spike is integrated into the fixed unit
mass `-int V_h'=1`; no limit, seminorm-uniform amplification,
or pointwise kernel estimate is needed.

After multiplying by the **signed** ideal Möbius coefficients `a_F(m)`
and summing finitely, the exact convolution `mu=chi_{-3}*a_F`
returns `M(N)`. Repeat the same calculation with
`(T,N)=(x,X_R)`, `(y,R-1)` and each
daughter site `m*q^2` at the common center x.
The same `h*x<1/2` works for all cases and yields the
WHOLE AMP coefficient sum before any absolute values.

**New Mathlib-only Lean entry point**
`VF_MID_919_OAI_INTEGRATED_SHARP_CHARACTER_STEP.lean` proves
an arbitrary signed, *finite* ideal-norm/rational-character
convolution is independent of the transition point u, and that
its integral against ANY signed density supported in the window is
exactly its sharp value times the total density mass. The
normalized-mass specialization is likewise proved. The module
does not import OAI's sixth-power amplification, establish the
global Dedekind dictionary or formalize the t-to-u change of
variables; those are separate interfaces. Its CI compilation
and axiom auditing are required before calling the new Lean
statements kernel verified.

**Analytic implication:** any useful bound must act on the
*integrated signed convolution or its completed Hermitian Gram*,
not on pointwise `J_{W_h}`. The exact integration can remove
the derivative spike completely but CANNOT, by itself, estimate
the recovered Mertens amplitude. The still-open uniform target is

```text
|A_R|^2 - D_R - Q_R^2 <= 2 E_R + C R^2 K,
A_R = - integral_1^infinity C_chi(t)/t * mathcal J_R(t) dt,
```

with all cross terms and the native negative-energy subtraction
retained. In particular, the stronger cancellation does NOT follow
from the published fixed-smooth sixth-power amplification lemma.
