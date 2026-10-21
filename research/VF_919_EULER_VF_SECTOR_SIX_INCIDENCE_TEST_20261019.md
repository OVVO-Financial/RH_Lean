# Exact Euler six-channel x original VF historical Sector Six: occurrence-level 6x6 test

**Date:** 2026-10-19. **Status:** exact finite numerical reindex, matched to named repo predicates; explicit shared-carrier restriction and theorem-level orientation obstruction. Not a proof of a six-way isomorphism of ALL Euler pair covariance, nor a Hecke sextic-character dictionary, nor an asymptotic covariance bound.

## 1. What was actually tested

For each VF shell I_R = (R²,(R+1)²), use the exact source classes:
  A = fixed-wheel smooth nonprime, H = high-prime composite, P = newly arriving prime.
Their full pair-covariance labels are AA,HH,PP,AH,AP,HP, with weight mu(n)*mu(m).

The **historical active VF physical source** on this shell is not the entire squarefree Mobius carrier. The compiled source \`vfMidOneBlockActivePhysicalCarrier\` contains the new prime sites and the already-processed odd least-owner squarefree composites. Thus at R>=3 it is precisely the odd squarefree sites of I_R; even squarefree sites are absent.

For EVERY unordered active pair (n,m):
1. Select the unique first-owner prime p = least prime where the squarefree factors of n,m differ; orient so a is p-free, child=p*b is p-divisible. Verify the lower signatures agree below p, a and p*b both lie in I_R, p*a>X, p*b<=X, X=(R+1)²-1.
2. Select r = largest remaining differing prime of (a,b), necessarily r>p. Strip r only from the coordinate it divides, producing the original native **orientation-preserving raw parent** (u,v). Verify no r divisibility remains in (u,v).
3. Apply the *literal repository chronological priority*: FIRST if p*u or p*v exits X; otherwise NEXT if r*u or r*v exits; otherwise RETURNED if p*r*u or p*r*v exits; otherwise completed (a completed active pair would fail the test). Assign LEFT priority whenever the left coordinate exits.
4. Add the pair's raw mu(n)*mu(m) to the 6x6 matrix, and **separately** its original VF physical charge(n)*charge(m), with charge = w_R - 1_Prime and w_R = [(2R+1)/log(R²+R+1/2)]/R. These two metrics are never identified with one another.

This uses the actual named definitions:
\`vfMidActiveReturnedPairCarrier\`, \`lowOwnerFirstOwnerBaseFiber\`,
\`lowOwnerFirstOwnerIncompleteFirstClipLeftSet\` etc.,
\`lowOwnerFirstOwnerPolarizationRawParent\`, the three
\`LowOwnerRawParent*Clipped\` predicates, and
\`vfMidOddSignedSeatCharge\`.
The finite verifier directly reimplements the predicates and audits every occurrence, not just aggregate totals. The historical raw-parent Fubini in the repo is already a Lean theorem; the **new numerical test** checks its intersection with Euler source classes.

## 2. Exact signed Euler incidence matrix: R=317

The columns are F-L, F-R, N-L, N-R, R-L, R-R = first/next/returned x left/right.

| Euler row | F-L | F-R | N-L | N-R | R-L | R-R | row sum |
|---|---:|---:|---:|---:|---:|---:|---:|
| AA | +193 | 0 | 0 | -128 | 0 | 0 | +65 |
| HH | +5,268 | 0 | 0 | -3,184 | +498 | 0 | +2,582 |
| PP | 0 | 0 | 0 | 0 | +1,431 | 0 | +1,431 |
| AH | -110 | 0 | 0 | -839 | 0 | 0 | -949 |
| AP | 0 | 0 | 0 | +702 | 0 | 0 | +702 |
| HP | 0 | 0 | 0 | -3,942 | 0 | 0 | -3,942 |
| **column sum** | **+5,351** | **0** | **0** | **-7,391** | **+1,929** | **0** | **-111** |

Exactly 258 active odd squarefree sites, 33,153 unordered pair occurrences; each matched once. The full squarefree shell has 387 sites, 74,691 unordered pairs, including 41,538 involving even squarefree sites. Full Euler signed covariance = -133; **unmatched signed covariance = -22**. The matrix has exact rank 3, witnessed by a nonzero 3x3 minor on rows AA/HH/PP and columns F-L/N-R/R-L.

## 3. Exact signed Euler incidence matrix: R=1027

| Euler row | F-L | F-R | N-L | N-R | R-L | R-R | row sum |
|---|---:|---:|---:|---:|---:|---:|---:|
| AA | +1,771 | 0 | 0 | -1,296 | 0 | 0 | +475 |
| HH | +41,406 | 0 | 0 | -29,239 | +2,872 | 0 | +15,039 |
| PP | 0 | 0 | 0 | 0 | +10,296 | 0 | +10,296 |
| AH | +565 | 0 | 0 | -6,340 | 0 | 0 | -5,775 |
| AP | 0 | 0 | 0 | +4,752 | 0 | 0 | +4,752 |
| HP | 0 | 0 | 0 | -25,200 | 0 | 0 | -25,200 |
| **column sum** | **+43,742** | **0** | **0** | **-57,323** | **+13,168** | **0** | **-413** |

Exactly 830 active odd squarefree sites, 344,035 unordered active pair occurrences; 1,252 full squarefree sites, 783,126 full pairs, **439,091 pairs involving excluded even sites**. Full signed covariance -426; **unmatched signed covariance -13**. Signed matrix rank 3.

The counts-only matrices and the original VF-weighted matrices are both independently generated. Under the ORIGINAL VF physical charges, the active-pair Gram totals are +20.271947386858326 at R317 and +234.33719886539825 at R1027. They independently match [(\sum_n charge(n))²-\sum_n charge(n)²]/2. These are **not** the mu-weighted signed covariance totals (-111,-413).

## 4. Exact structural obstruction: three native orientations vanish

The tests at R=2,3,5,7,13,31,56,101,317,439,1027 found ZERO pair occurrences in first-RIGHT, next-LEFT and returned-RIGHT. This is not numerical happenstance.

Let the active p-free site a be clipped (p*a>X) while its true returned child p*b is admitted (p*b<=X). The greatest remaining new prime r divides **exactly one** of a,b:

- If (a,b)=(r*u,v), then r*u<=X; p*r*u>X and p*v<=X. This rules out FIRST-RIGHT, NEXT-LEFT and RETURNED-RIGHT. Remaining possibilities are FIRST-LEFT, NEXT-RIGHT and RETURNED-LEFT.
- If (a,b)=(u,r*v), then p*u>X. The very first classification is FIRST-LEFT, regardless of other exits.

This proves the **shared-current-active-carrier** incidence matrix has at most THREE nonzero columns and hence rank at most 3 for EVERY block where the hypotheses hold. Actual integer samples R317 and R1027 have rank exactly 3. The paired Lean source \`research/VF_919_EULER_SECTOR_SIX_ACTIVE_SUPPORT_20261019.lean\` proves both forbidden-sector conditions against the **original** native \`lowOwnerFirstOwnerIncomplete*Left/RightSet\` predicates; the full occurrence-level match is separately verified by the finite script.

**Do not mistake this for a theorem that the original six-sector boundary is globally only three sectors**: other historic, non-active, off-block or differently oriented parent carriers may populate the other columns. This support restriction is for the literal current clipped x admitted active shared carrier only.

## 5. Quantitative consequences

- **Genuine one-to-one occurrence reindex on the shared carrier:** yes. Row totals equal restricted six-channel Euler covariance, and column totals equal chronological/orientation reindex of the *same* atoms. Every active pair has exactly one (p,signature,r,parent,orientation), with no completed residual.
- **Invertible 6x6 Euler-to-Sector-Six map:** NO, because the three columns above are identically zero.
- **Complete Euler six-channel Gram equals this original VF historical source:** NO. At R317 and R1027 the signed contributions from even squarefree pairs are -22 and -13 respectively (far more unmatched pair *counts*).
- **Full original VF weight transfer from pure mu weights:** NO unless original VF charge scalars are preserved site by site. The program tests the two separately.
- **OpenAI sextic/Hecke six phases:** these are a third, different carrier. No canonical bijection or all-scale OAI moment bound is furnished by this finite source reindex.

## 6. Reproduce

\`\`\`sh
python3 scripts/vf919_euler_historical_six_by_six.py --roots 317 1027
python3 scripts/vf919_euler_historical_six_by_six.py --roots 2 3 5 7 13 31 56 101 317 439 1027
\`\`\`

The test writes signed, occurrence-count, and original VF charge 6x6 CSVs and a JSON audit summary. It checks the complete row-marginal Gram, independent diagonal, unique prime-owner assignments, complete historical exit classification, exact historical 317/1027 6x6 reference entries, 3x3 minor nonvanishing and all excluded even-site charges. New CI compiles the two original-predicate Lean obstruction lemmas warnings fatal with standard axiom footprints.

**Next test:** attempt an **augmented carrier** including the even and other historical populations, with separate explicit source-tag and sign coordinates. The resulting operator is expected to be rectangular and occurrence/multiplicity preserving, not a 6x6 permutation.

## 7. Exact odd-carrier sufficiency and prime-row compression (2026-10-19)

**Lean:** `research/VF_919_EULER_ODD_CARRIER_PRIME_ROW_20261019.lean`.
The proof REUSES `RHLean/Arithmetic/MoebiusDoubling.lean` and the existing
`sum_Icc_eq_odd_add_even`, `sum_evenCofactorPrefix_eq_neg_odd_half`,
and `cofactorMobiusPrefixMass_eq_mertensSummatory` theorems. It neither
defines a new even-site incidence matrix nor assumes a cancellation estimate.

Write (O(X)=\sum_{1\le n\le X,\;n\text{ odd}}\mu(n)). The exact identity is

\[
M(X)=O(X)-O(\lfloor X/2\rfloor).
\]

It follows that proving an odd-prefix (O_\varepsilon(X^{7/8+\varepsilon}))
bound suffices for the full Mertens bound. The reduction itself proves NO
such bound. The Lean module records the exact complex canonical equality,
its real-part equality, and an explicit norm envelope using both odd prefixes.
The named existing `mertensSummatory` is the actual physical Möbius sum.

For the actual odd-carrier shell, let (A,H\) be the signed smooth and
high-prime composite masses, (Q\) the integer number of new primes,
and (S=A+H-Q\). Then, identically,

\[
\underbrace{PP+AP+HP}_{C_{\mathrm{prime}}}
=\tfrac12Q(Q-1)-AQ-HQ
=-\tfrac12Q(Q+1)-QS.
\]

Let (C_{\mathrm{comp}}=AA+HH+AH\). The *fully signed* shell covariance
becomes (C_{\mathrm{odd}}=C_{\mathrm{comp}}+C_{\mathrm{prime}}\);
this is a two-bill reorganization of six exact source rows, NOT an
inequality or a sixfold incidence isomorphism.

| R | Q | S odd | AA+HH+AH | PP+AP+HP | total odd C |
|---:|---:|---:|---:|---:|---:|
| 317 | 54 | +6 | +1698 | -1809 | -111 |
| 1027 | 144 | -2 | +9739 | -10152 | -413 |

The reproducible 6x6 Python census now asserts the prime-row formula,
the composite-plus-prime reassembly, and the *global* odd-prefix identity
at the exact (X=(R+1)^2-1\) cutoff for EVERY tested root.

**Important PNT correction:** Ordinary PNT does NOT give
(Q_R\sim R/\log R\) uniformly in each individual square shell. Those
intervals have length about (\sqrt x\), shorter than a directly
PNT-controlled relative interval. But PNT DOES give, on the dyadic range
(H\le R<2H\),

\[
\sum_{R=H}^{2H-1}Q_R\sim\frac{3H^2}{2\log H}.
\]

By Cauchy--Schwarz and (PP_R=\binom{Q_R}{2}\),

\[
\sum_{R=H}^{2H-1}PP_R
\ge \frac1{2H}\Big(\sum_R Q_R\Big)^2
-\frac12\sum_R Q_R
\gg\frac{H^3}{(\log H)^2}.
\]

Thus a strategy bounding positive prime-pair cells separately cannot
supply the desired dyadic (H^{5/2+\varepsilon}\) signed-energy scale
(for any fixed (\varepsilon<1/2\)); cancellation with other signed rows
is **mathematically necessary**, not merely a numerical observation.
The (H^{5/2+\varepsilon}\) dyadic energy gate is already recorded in
`VF_919_SEVEN_EIGHTHS_DYADIC_SHELL_COVARIANCE_20261019.lean`.

**Outstanding analytic step:** prove a genuinely unconditional
signed dyadic control of (\sum_{H\le R<2H}(S_R^{\mathrm{odd}})^2\)
at (O_\varepsilon(H^{5/2+\varepsilon})\), or an equivalent
one-sided signed covariance budget. The current identity still contains
(S\) on the right, so a bound derived by merely rearranging
(C_{\mathrm{prime}}\) would be circular. The VF fractional charges
must also remain distinct from the true Möbius signs.

## 8. Rank-one drift and canonical greatest-prime fibers (2026-10-19)

**Source:** `research/VF_919_EULER_RANK_ONE_GPF_FIBERS_20261019.lean`;
the numerical script now also checks all distinct greatest-prime-factor fibers.
The new file imports the existing canonical cofactor factorization infrastructure
and contains nine additional native theorem footprints, raising the dedicated
CI gate from 48 to **57**.

Set `T_R = A_R+H_R`, `Q_R=#P_R` and `S_R^{odd}=T_R-Q_R`.
For ANY real deterministic reference function `L_R`, put
`t_R=T_R-L_R`, `q_R=Q_R-L_R`. There are **two independent exact
algebraic facts** (no new hypothesis or positivity assertion):

```math
\sum_{H\le R<2H}(T_R-Q_R)^2
=\sum_{H\le R<2H}(t_R-q_R)^2,
```

```math
2\sum_R T_RQ_R
=2\sum_R L_R^2+2\sum_R L_Rt_R
 +2\sum_R L_Rq_R+2\sum_R t_Rq_R.
```

The drift terms in the second identity are **not automatically negligible**
and no inequality has been gained. A choice
`L_R=\lambda_H(2R+1)` with
`\lambda_H=\sum_R Q_R/(3H^2)` gives
`\sum_R(Q_R-L_R)=0` and by ordinary PNT
`\lambda_H\sim 1/(2\log H)` (since the original root band
`H\le R<2H` has `\sum_RQ_R\sim 3H^2/(2\log H)`).
This provides an exact, auditable choice of baseline, not a variance bound.
(Using `L_R=R/\log R` is a close finite illustration, not an assumption.)

### The true prime/cofactor incidence

For `R>=2`, every admitted odd squarefree `n` belongs to precisely
one canonical fiber with `m=n/P^+(n)` and `q=P^+(n)`, satisfying
`q` prime, `P^+(m)<q`, and `n=mq`.
Write `Q_R(m)` for the **number of distinct greatest-prime-owner
occurrences** in that fiber. The Lean file proves that the prime-owner
coordinate is injective in each fiber, and proves finite canonical Fubini:

```math
S_R^{odd}=-\sum_{m\ge1}\mu(m)Q_R(m),
\qquad
T_R-Q_R=-\sum_{m\ge1}\mu(m)Q_R(m).
```

All sums are finite (the code uses `m<(R+1)^2`). The cofactor
`m` need NOT be smaller than `q`: `n=105=15\cdot7`, for
example, has `P^+(15)=5<7` but `15>7`. Replacing `P^+(m)<q`
with `m<q` would silently exclude valid composite fibers. Conversely,
dropping the greatest-prime condition entirely would double-count
composites. The `m=1` fiber counts actual odd primes; all remaining
fibers are genuine odd composites.

The cross row has the exact cofactor form

```math
AP_R+HP_R=-Q_RT_R
=Q_R\left[\sum_{m\ge1}\mu(m)Q_R(m)-Q_R\right]
=Q_R\sum_{m>1}\mu(m)Q_R(m).
```

The last equality uses `Q_R(1)=Q_R`; the Lean file proves the first
two expressions by canonical Fubini, while the finite census checks
the final prime-only specialization at every tested root.

For each fiber, `Q_R(m)` is the number of primes `q>P^+(m)` with
`R^2\le mq<(R+1)^2`, **not** merely the unrestricted number of
primes in `[R^2/m,(R+1)^2/m)`. Therefore a small-cofactor
heuristic `Q_R(m)\approx Q_R(1)/m` is not a uniform consequence of
PNT: the individual dilated intervals may be shorter than any interval
for which a useful relative PNT remainder is known. The conditionally
convergent identity `\sum_{m\,odd}\mu(m)/m=0` is a global statement,
not a license to interchange the short-interval and cofactor sums.

### The signed analytic acceptance criterion

For `Q_R(m)` with the true greatest-prime cutoff, the remaining
quantity is the *full signed cofactor-collision* form:

```math
\sum_{H\le R<2H}
 \sum_{m_1,m_2\ge1}\mu(m_1)\mu(m_2)
 Q_R(m_1)Q_R(m_2)
=\sum_{H\le R<2H}(S_R^{odd})^2.
```

The desired independent estimate is
`O_\varepsilon(H^{5/2+\varepsilon})`. No proof of this estimate is
claimed. Summing `Q_R(m_1)Q_R(m_2)` absolutely loses the necessary
Möbius cancellation and is the wrong inequality direction.

**PNT inference guardrail:** Ordinary PNT proves
`\sum_RQ_R\sim 3H^2/(2\log H)` and therefore
`\sum_RQ_R^2\gg H^3/(\log H)^2`. It does *not* independently prove
`\sum_RT_R^2\sim\sum_RQ_R^2` or a matching cross energy.
If the desired dyadic energy bound is assumed, Cauchy gives
`|\sum_RQ_R(T_R-Q_R)|\le
 (\sum_R Q_R^2)^{1/2}(\sum_RS_R^2)^{1/2}`, with an error
of order `H^{11/4+\varepsilon/2}/\log H` if one also has
the expected prime-square second moment. That is generally **larger**
than an `H^{5/2+\varepsilon}` error and must not be silently replaced
by one. The required savings remain genuinely analytic.

**Exact independent numerical audit, reproduced on the true odd sites:**

| R | T_R | Q_R | S_R | distinct canonical m-fibers | composite-prime AP+HP |
|---:|---:|---:|---:|---:|---:|
| 317 | 60 | 54 | +6 | 112 | -3240 |
| 1027 | 142 | 144 | -2 | 368 | -20448 |

The finite test asserts `Q_R(1)=Q_R`, signed Fubini, one-to-one
prime ownership, `\mu(mq)=-\mu(m)`, the exact composite-only identity,
and centered energy with `L_R=R/\log R`.


## 9. Finite double-difference kernel and strict-cutoff local dipoles

The Lean module research/VF_919_EULER_RANK_ONE_GPF_FIBERS_20261019.lean
now adds gpf_one_fiber_eq_prime_count, dyadic_kernel_double_difference_eq,
and gpf_mul_prime_of_lt_gpf, plus seven supporting theorem footprints.
The dedicated CI checks 67 Lean theorem footprints.

For any finite cofactor set M and deterministic alpha, let
Delta_R(m)=Q_R(m)-alpha(m)*Q_R(1),
c_M=sum_{m in M} mu(m)*alpha(m), and
B_R=sum_{m in M} mu(m)*Delta_R(m).
Then A_R=sum_m mu(m)*Q_R(m)=B_R+c_M*Q_R(1).
The exact finite double-kernel identity is:

\[
\sum_{m,n\in M}\mu(m)\mu(n)K_H(m,n)
=\sum_{m,n\in M}\mu(m)\mu(n)K_H^\Delta(m,n)
+2c_M\sum_R Q_R(1)B_R+c_M^2\sum_R Q_R(1)^2.
\]

Here K_H(m,n)=sum_R Q_R(m)Q_R(n), and
K_H^Delta(m,n)=sum_R Delta_R(m)Delta_R(n).
If alpha(1)=1, K_H^Delta(1,m)=K_H^Delta(m,1)=0.
The defect-zero corollary is conditional on c_M=0.

**Defect zero is not the analytic estimate.**
A simple purely algebraic choice alpha(1)=alpha(3)=1 and alpha(m)=0
otherwise on a carrier containing 1 and 3 gives c_M=0 but
B_R=A_R, with no variance saving. The verifier independently checks
the full three-term identity with alpha(m)=1/m, as well as this
zero-defect/no-saving example.

**Exact greatest-prime cutoff:** for d>1, p prime,
p<P+(d) implies P+(p*d)=P+(d). This is true even for d>p and
does not require p to be fresh. The Möbius sign reversal
mu(p*d)=-mu(d) additionally requires p not dividing d.
Both fiber counts then use the same prime lower threshold
q>P+(d), but different dilated physical intervals.

For p=3, the globally defined odd-squarefree cofactors with P+>=5
pair as {d,3d}, 3 not dividing d, with opposite signs.
**The finite active cofactor set in a given shell or dyadic band is
not generally closed under d -> 3d.** One fiber can be present when
the other is absent. This is a genuine boundary contribution,
not a counterexample to greatest-prime cutoff preservation.
The Python verifier checks exact sign/cutoff invariance and records
unmatched finite-shell parents.

The prime-only identity Q_R(1)=Q_R is now explicitly a Lean theorem
for R>=2, closing the earlier requested base-fiber specialization.

**Open:** A signed analytic moment/compensation estimate strong
enough for sum_{H<=R<2H}(S_R^odd)^2
=O_epsilon(H^(5/2+epsilon)). No pointwise Poisson variance,
short-interval PNT, or square-root saving is claimed.


## 10. Exact 3-dipole zero defect and physical cofactor hyperbola (2026-10-19)

New Lean file: VF_919_EULER_THREE_ADIC_HYPERBOLA_20261019.lean.
Twelve new theorem footprints raise the dedicated CI gate to 79.

**Finite rational defect.** Take D_M to be the odd squarefree
integers d in [1,M] not divisible by 3, and C_M = D_M union 3*D_M.
The parent and child sets are disjoint and the map d -> 3d injective.
Define alpha(d)=1/d, alpha(3d)=1/d and zero elsewhere.
The theorem three_adic_dipole_defect_eq_zero proves the literal
existing kernel defect, with NO asymptotic assumption:

\[
\sum_{m\in C_M}\mu(m)\alpha(m)
=\sum_{d\in D_M}\frac{\mu(d)+\mu(3d)}d=0.
\]

The zero-defect instance of the existing double-difference theorem
then applies to **C_M only**; an arbitrary clipped active cofactor
carrier may omit one member of a pair. Critically, alpha(3d)=1/d
is NOT the natural 1/(3d) relative prime-density coefficient:
zero defect does not imply small compensated variance. The base
pair {1,3} does not share a greatest-prime cutoff, since P+(1)=1
and P+(3)=3. That is handled separately by the small-cofactor
automatic cutoff, not the parent-child invariance lemma.

**Full-carrier extension (the essential closure).**
The initial pair-complete identity alone cannot be substituted into the
global kernel over all cofactor indices. The new theorems
vf919ThreeDipoleCarrier_subset_range and
three_adic_dipole_full_defect_eq_zero prove that when 3M<U,
alpha is supported on C_M inside the FULL Finset.range U and vanishes
identically outside C_M. Thus
\[
\sum_{m<U}\mu(m)\alpha_M(m)=0
\]
as an exact identity on the actual large finite ambient cofactor set.
The theorem three_adic_dipole_full_dyadic_kernel_exact then applies
the double-difference identity on the FULL cofactor range
U=(2H)^2 for H<=R<2H, assuming 3M<H. This removes the scalar defect
and both drift-error terms from the complete finite signed kernel;
it does NOT establish a bound for the remaining centered energy.
It does not require the NONZERO-FIBER active subset to be pair-closed:
absent fibers contribute Q_R(m)=0 and alpha is still defined on the
ambient carrier.

**Automatic small-cofactor cutoff.** If 3M<H<=R, 0<m<=3M,
q is prime and R²<=mq<(R+1)², then q>m, so P+(m)<q
and P+(mq)=q. The unrestricted pi-difference therefore represents
Q_R(m) when m is **odd and squarefree**; even or squareful m
are excluded from the true odd-squarefree carrier despite the
possibility of primes in the corresponding dilated interval.

**Exact hyperbola and high-owner Fubini.** The Lean theorem
odd_shell_hyperbola_split_eq partitions actual odd squarefree
shell sites into cofactor m<=3M and m>3M. The theorem
odd_shell_high_tail_dual_by_gpf regroups the latter by the unique
greatest prime q, retaining the signed cofactor mu(m) and
the genuine P+(m)<q cutoff in every term:

\[
S^{odd}_{R,high}(M)
=-\sum_{q<(R+1)^2}
 \sum_{\substack{R^2\le n<(R+1)^2\\
 n\ {\rm odd\ squarefree}\\
 P^+(n)=q,\ n/q>3M}}\mu(n/q).
\]

This is exact q-owner site-indexed Fubini, not an analytic estimate.

**Unproved analytic step and two corrections.**
No unconditional sieve estimate of the required centered prime
variance or signed smooth-cofactor moment is established.
The proposed illustration M² H² is H³ when M~H^(1/2);
only M<=H^(1/4) would attain H^(5/2) by that budget.
And m>3M with M~H^(1/2) gives only q<O(H^(3/2)),
not q<=H: the corresponding m-window length H/q may be
less than one. Thus neither half automatically has sufficient
interval length for prime or Möbius square-root cancellation.
For a genuinely fixed small q, squarefree m with P+(m)<q
divides a finite primorial, so m cannot grow like H².

The Python 6x6 verifier additionally asserts the rational
pair-complete defect, physical low/high mass identity,
low-cofactor q>m, and exact high q-owner regrouping.
