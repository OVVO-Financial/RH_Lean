# Canonical low/high gate extension: weighted NNS and a uniform root boundary

**2026-10-21 · stacked follow-up to PR #998.**
This is finite arithmetic and exact coefficient algebra, not an
RH proof, a new 7/8 moment estimate or a probabilistic independence hypothesis.

## 1. Already-proved canonical low count, newly extended to arbitrary complex weights

The existing SignedHeight.card_le theorem proves that a square block
B_n=[n²,(n+1)²) contains no more than 1+floor(H/n) canonical factor
pairs with Z(m)=|q²-c²|/2<=H, m=cq and q=P+(m).

The accompanying new Lean theorem weightedCanonicalLow_energy_le
upgrades this to arbitrary complex amplitudes a_m on a faithfully
one-to-one canonical factor-pair carrier:

    |sum_low a_m|² <= (1+floor(H/n)) * sum_low |a_m|².

For H=Lambda*n the squared summation operator norm is <= Lambda+1,
regardless of phase, signs or variation in the individual weights.
The more elementary L-infinity counterpart is also formalized.

This does NOT automatically apply to the multiple ideal-labelled
columns of the production OpenAI Hecke detector. A phase- and
multiplicity-preserving map from original columns to canonical factor
pairs is required and remains an explicit separate obligation.

## 2. NEW: the globally high-prime source barely intersects the canonical low gate

Fix R>=2, X=R²-1 and an integer Lambda>=0. If a factor pair m=cq<X
has GLOBAL high prime q=P+(m)>R but LOCAL height
Z(m)<=Lambda*n where n=floor(sqrt(m)), then:

- c<R because cq<R² and q>R;
- d=q-c>=2;
- the previous proven gap inequality gives d*n<=Z(m)<=Lambda*n,
  hence d<=Lambda;
- therefore R<q=c+d<R+d<=R+Lambda and R<c+Lambda.

This is the NEW highOwner_lowHeight_gap_fence theorem in Lean.
It says low-height/high-prime overlap is confined to a microscopic
fixed-width neighbourhood of the square-root cutoff.

At a fixed d from 2 to Lambda there are at most d-1 possible
values for q in {R+1,...,R+d-1}; the cofactor c=q-d is then
uniquely determined. Consequently the total overlap across ALL
integers m<=R²-1, not merely one square block, satisfies

    count(high global prime AND low canonical height)
      <= Lambda*(Lambda-1)/2.

This sharp count is an elementary paper corollary, not yet a separate
Lean cardinal theorem. It does not even require q to be prime or
m to be squarefree to obtain the upper bound.

The stronger Lambda=2 intersection is EMPTY, since d is forced to
equal 2 and the height inequality yields c+1<=n, contradicting
n²<=c(c+2)=(c+1)²-1.
highOwner_lowHeight_two_impossible records this in Lean.

If the original integer-atom weights obey |a_m|<=B, then the total
overlap amplitude is at most B*Lambda*(Lambda-1)/2 uniformly in R.
That is an O_Lambda(1) boundary leakage statement, not a
high-sector dispersion estimate.

## 3. Independent true-Mobius sieve

Linear Mobius/least-prime sieve with exact greatest-prime cofactors,
tested through R=3162 and x=9,998,243:

| R | Lambda | Low count | Low signed | Complement signed | High-prime low overlap | Uniform cap |
|---:|---:|---:|---:|---:|---:|---:|
| 317 | 2 | 47 | +3 | -31 | 0 | 1 |
| 317 | 5 | 262 | -52 | +24 | 0 | 10 |
| 1027 | 2 | 129 | +3 | +364 | 0 | 1 |
| 1027 | 5 | 722 | -124 | +491 | 0 | 10 |
| 3162 | 2 | 337 | +17 | +1048 | 0 | 1 |
| 3162 | 5 | 1901 | -207 | +1272 | 1 | 10 |
| 3162 | 10 | 4199 | -451 | +1516 | 5 | 45 |

At R=3162, Lambda=5 the sole crossover integer is
3163*3161=9,998,243, with gap d=2 and Mobius weight -1.

The ordinary signed low/high decomposition at the same endpoint is

    M(9,998,243) = (-207) + (1272) = 1065.

Its exact cross term in the squared zero-target Gram is

    2*(-207)*(1272) = -526,608.

Therefore separately norming the sparse low and unsolved high
source loses a genuine, large signed interaction.

## 4. TWO physical admission gates, not a fabricated single OAI mask

The original OAI marked-minus-rescaled coefficient generally has
different physical window masks on its A and B branches. For the
original labelled complex atoms a_i,b_i, with masks g_A,g_B, the
exact total is the sum of three disjoint faces:

    admitted both:       (a_i - b_i)
    admitted only A:     a_i
    admitted only B:    -b_i

The new twoAdmissionGates_exact_three_faces theorem formalizes this
without assuming masks or weights coincide. The retained phase
defect on the BOTH face and the two unmatched boundary faces are
the exact remaining source-level analytic tasks. Apply the PR #998
NNS Co/Div ledger on ALL original coefficients without double
weighting W or dropping cross-face Gram terms.

## 5. The remaining arithmetic obstacle

The low-height/high-owner intersection is O_Lambda(1), but most
squarefree integers lie in the high-height population. Neither
the overlap count nor PNT-relative Co/Div equality controls its
signed Gram to RH scale. The needed separate statement is still
a uniform weighted high-height source energy AND the coupled
low/high cross-energy or a preserving matched-return estimate.

A future valid OpenAI transfer must preserve: selected-prime
subset, full ideal labels and multiplicity, conductor phase,
original rescaled masks, physical windows and exact D_U
normalization. No such full transfer is asserted here.

**Source authority:**
RHLean/Proof/SignedCanonicalHeight.lean;
research/VF_919_ACTUAL_WEIGHTED_NNS_COVARIANCE_KERNEL_20261021.lean;
openai/math/lean/OAI/NumberTheory/DirichletL/Detector/GaussianCompensation.lean;
research/EULER_PRIME_COMB_FEEDBACK_FINITE_C.md.
