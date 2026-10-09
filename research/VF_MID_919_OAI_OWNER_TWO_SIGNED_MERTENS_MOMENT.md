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

### Existing OAI inverse moments do not yet save the principal row

The paper's "Marked inverse moment" (Section "The inverse moment with prime
factors", Lemma old-eq:4.1) estimates, with no selected prime factors,

\[
 M_u(Z^r;W)=Z^{-r/2}
   \sum_{\mathfrak n}\mu_F(\mathfrak n)\psi_u(\mathfrak n)
     W(N\mathfrak n/Z^r),\qquad
 \sum_{0<N u\ll Z^m}|M_u|^2\ll Z^{m+\epsilon}
\]
under r <= m-c_1 (and the second displayed range condition).
Taking the single principal row u=1 only yields
\[
 \left|\sum_{\mathfrak n}\mu_F(\mathfrak n)
     W(N\mathfrak n/Z^r)\right|
 \ll Z^{(m+r)/2+\epsilon}.
\]
Since m>r, this is NO better than a length-Z^r trivial power.
Even before incorporating the chi_{-3} convolution B11 and the second
Mertens factor in B1, the *existing averaged moment* cannot prove the
needed principal-row saving merely by selecting one row.

The concrete new analytic work is therefore **a principal-row
amplification/correlation theorem for the quadratically convoluted
B11 coefficients**, compatible with the TWO original Möbius factors
in B1/B6 and the signed native mixed boundary. Neither the published
mean-square bound nor phase-preserving C-to-R realification alone
establishes that statement.

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
