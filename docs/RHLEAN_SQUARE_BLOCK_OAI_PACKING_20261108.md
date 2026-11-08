# Square blocks as the atomic arithmetic partition of fixed OAI slots

Date: 2026-11-08. Status: **new proof candidate, verified only after warning-fatal
Lean and dependency checks on PR head**. Does not assert RH, q(X)->0 or finite A.

## 1. Two different partitions, and an exact bridge

The physical square block is B_r={r²,...,(r+1)²-1}. For EVERY
integer-valued signed sequence f and all a<=b, the exact regrouping is

    sum_{a²<=n<b²} f(n) = sum_{a<=r<b} sum_{r²<=n<(r+1)²} f(n).

The new Lean theorem is groupedSquareBlocks_sum. In particular f=mu recovers
each completed square-group Möbius contribution without absolute values or
any prime-count approximation. This is an exact additive partition.

An OAI detector slot is NOT one arithmetic square block. OAI's ell_j
locates an original prime-ideal norm ray, roughly N(P)~Z^ell_j;
the smooth profile and Hecke-character weights are part of the source.
Each such norm ray typically occupies many square blocks.

**EXISTING exact bridge: already paid, not an open task.** The repo has
vf919OAITrueSquareIdealNormSource_eq_originalShell and its complete
signed covariance (VF_919_OAI_TRUE_IDEAL_NORM_SHARP_SQUARE_BLOCK_20261019.lean);
rhlean_actual_ideal_ordered_physical_square_pairs_eq_VF919
(RHLeanActualEisensteinIdealSharpSquareBlock.lean); and
rhlean_actual_sharp_compensated_full_ideal_pair_gram
(RHLeanActualEisensteinCompensatedSharpSquareBlock.lean).
OAI_PAIRED_SHARP_EULER_SQUARE_LOCALIZATION_20261028.lean already
identifies the true sharp source with three moving Euler populations.

The **unpaid bridge is quantitative smooth-to-sharp uniformity**:
the OAI licensed smooth marked/inverse profile moment theorems do not
automatically bound the original sharp root-indexed dyadic energy
sum_{H<=R<2H} |M((R+1)^2-1)-M(R^2-1)|^2 with the needed power saving.
See research/OAI_PAIRED_SHARP_MOMENT_TRANSFER_20261028.md and
research/OAI_SHARP_ROOTGRID_HEIGHT_AUDIT_20261028.md.
The elementary grouping theorem is not a replacement for those paid
coefficient/covariance bridges and provides no new cancellation.

## 2. The detector's necessary slot-count tax

Let 0<L and ell_j in (0,L) be N distinct widths summing to 1/6. Summation
forces N L>1/6, hence N>1/(6L). The existing *explicit* profile chose

    N_old = ceil(max(1,1/(3L)))+2.

This is almost twice the necessary count as L->0. One cannot identify
N with the number of physical B_r as x grows: that count is ~sqrt(x),
and the fixed-source gain would fall to zero if N were replaced by sqrt(x).

## 3. A better distinct near-uniform finite source

Construct

    N_new = ceil(max(1,1/(6L)))+2  >=3,
    w_j = 1 + j/N_new²  for j=0,...,N_new-1,
    W = sum_j w_j,
    ell_j = w_j/(6W).

Since N<=W<=N+1 and 1<=w_j<1+1/N:

- ell_j>0 and injective;
- sum_j ell_j=1/6 exactly;
- ell_j >=1/(6(N+1)) >=1/(8N);
- ell_j < (1+1/N)/(6N) = (N+1)/(6N²);
- (N+1)/(6N²) < 1/(6(N-1)) < L
  because N-1>1/(6L) and (N+1)(N-1)<N².

This is an elementary new geometry witness, needing NO new analytic moment
input. The source is constructed in the *original* HighData type using the
same explicitDelta=1e-6, explicitT=1e-8, original detector mesh,
original slot normalization sum=1/6, and all existing window, phase,
height, epsilon, central and principal budgets.

The previously merged complete original source theorem states

    beta <= 7/8 - actualSlotMinimum(D)/4.

Therefore the construction claims a new theorem

    beta <= 7/8 - 1/(32*N_new).

Its Mertens consequence still allows every positive exponent loss.
Because N_new<=N_old (ceil monotonicity), the new saving is at least
1.5 times the original conservative 1/(48*N_old) and approaches a factor
3 improvement when the detector cap L is tiny. These comparisons of
integer ceilings are elementary but are not separately Lean-named.

## 4. What this does NOT do

The unchanged original detector requires ell_j<=t/200, with t=1e-8
for the explicit source. Consequently even an *ideally packed* source
with this fixed t cannot have

    tau=actualSlotMinimum(D)/4 > t/800 = 1/80,000,000,000.

In particular, this repacking CANNOT by itself supply the 1/8 saving
needed to go from Mertens exponent 7/8 to 3/4, much less RH. The
meaningful next independent arithmetic theorem would compare the
ORIGINAL signed OAI row/Hecke source to grouped NATURAL square-block
Euler/Möbius populations with quantitative control of its character
weights, norm fibers, boundary collars and mixed terms. Proving an
identity is insufficient; a bound surviving the complete LOW/HIGH and
principal source is required.

## 5. Verification and prohibitions

The PR adds warning-fatal Lean compilation of
VF919ExplicitSquareBlockPacking.lean, exact type checks for the block
sum and terminal exponent, and standard-axiom audits. It reuses the
unchanged existing source-pinned original OAI full endpoint and original
native Mertens transfer. No sorry, admit, extra axiom, target-defined
hypothesis, unproved finite-A conclusion, altered pinned OpenAI source,
or silent ideal/rational identification is allowed.
