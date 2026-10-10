# #925 — Every integer cutoff: original VF physical Sector Six, roots 17–1027

**October 10, 2026. FINITE exact-arithmetic census and new square-band geometry. NOT RH.**

The independent complete diagnostic is distributed as
\`VF925_Square_Clipping_17_1027_Full_Sector_Six_Audit.zip\`
in the research conversation, with \`vf925_square_cutoff_sweep.py\`,
\`vf925_full_sector_six_sweep.py\`, and
\`vf925_sector_smallroot_scan.py\`, all output CSVs and visualizations.
These are finite sample computations, not native all-root Lean proofs.

## What is clipped, and what is not

For \(R^2\le x\le(R+1)^2\), include each actual odd physical
source \(n\in(R^2,\min(x,(R+1)^2))\), with **unchanged**
\(z_R(n)=w_R-\mathbf1_{\rm Prime}(n)\) and
\(w_R=(2R+1)/(R\log(R^2+R+1/2))\). Preserve the ONE
historical anchor \(-D_R\) and squareful positive physical sources.
At intermediate x this discrete odd-site prefix differs from the
continuous VF live mass; the script records both and checks their
deterministic difference.

On the squarefree physical source, form each UNORDERED pair of
distinct original odd sites \(a,c\) exactly once. Its first separating
prime p and the p-free cofactor b with c=p*b give the actual
clipped-base x admitted-returned-child coordinates of
\`vfMidActiveReturnedPairCarrier\`. The greatest fresh prime r
of (a,b), and its two raw parents obtained by literal r-removal,
give the original six sector orientation tests. These are the
same *formulas* as the repo's
\`LowOwnerRawParentFirstOwnerClipped\`,
\`LowOwnerRawParentNextOwnerClipped\`,
\`LowOwnerRawParentReturnedNextClipped\`, with left priority.

For this exact current physical square band, the original AMP
Dirichlet weight on each of a and p*b is 1; the p*a corner clips.
The double Möbius signs in the returned atom reduce the native
weighted atom to \(\boxed{z_R(a)z_R(pb)}\). This is a concrete
source-to-boundary coefficient computation, not an extra parent
charge. At variable x the common clock has the literal cutoff
\(X=\min(x,(R+1)^2-1)\) while the root threshold remains R+1;
the production endpoint is the rightmost cutoff.

The measured original Co/Div excess is independently reassembled
at EVERY tested x, including original diagonal, squareful and
once-only historical anchor terms:

\[
E(x)=\mathrm{Residual}(x)+4 Z(x)-2A(x),
\]

with \(Z=\sum_{i<j}z_i z_j\) partitioned by the three nonzero
sectors, and \(A=\sum_{i<j}|z_i z_j|\). This is the exact ORIGINAL
quadratic physical source, not merely a linear wheel telescope.

## Full cutoff witnesses

| Root | Values x tested | Squarefree physical pairs | First-left | Next-right | Returned-left | Other orientations |
|---:|---|---:|---:|---:|---:|---:|
| 17 | 289..324 (36) | 105 | 38 | 50 | 17 | 0 |
| 56 | 3136..3249 (114) | 990 | 330 | 571 | 89 | 0 |
| 119 | 14161..14400 (240) | 4656 | 1888 | 2483 | 285 | 0 |
| 317 | 100489..101124 (636) | 33153 | 12157 | 19067 | 1929 | 0 |
| 1027 | 1054729..1056784 (2056) | 344035 | 129350 | 201517 | 13168 | 0 |

The **finished-block SIGNED pair masses** at R=17 are:
FL=+4.91403, NR=-11.51448, RL=+5.00626.
At R=317: +367.51760, -1338.94382, +991.69817;
at R=1027: +2692.22155, -10057.17454, +7599.29019.
All original Co/Div excesses reconstructed, including independent
historical/squareful residual:
-72.92846, -13423.78466, -105561.28136 respectively.

## Explicit three-sector physical incidence reduction

For any x in these tested windows, let P_x be actual prime odd
sites and C_x the active squarefree composite sites. The actual
classification places all prime-prime pairs in returned-left
and every prime-composite pair in next-right. If F_x,N_x,T_x
are the numbers of composite-composite pairs in first-left,
next-right, returned-left, respectively, then

\[
\boxed{
Z_{FL}=w_R^2 F_x,\quad
Z_{NR}=w_R^2 N_x-w_R(1-w_R)P_x C_x,\quad
Z_{RL}=w_R^2 T_x+(1-w_R)^2 {P_x\choose 2}.
}
\]

**THIS IS THE ARITHMETIC SOURCE OF THE LARGE NEGATIVE next-right
PAYMENT IN THE SAMPLED FULL BLOCKS.** It is a genuine prime-vs-composite
pair interaction, NOT independent historical q payments. The
classification and coefficients have a direct finite verification;
no estimate of P_x or N_x has been proved.

## The block-position result

In seven detailed blocks and in 193 CONSECUTIVE roots R=8..200:
**880,374 literal physical pairs, ZERO migrations among clipping
sectors after both sites enter**, and ZERO contributions in the other
three candidate sectors.

The new unconditional Mathlib-only lemma
\`vfWilesOddBandNextRightClip_noIntermediate\`
provides the number-theoretic geometric reason: if a=r*h
and c=p*b are odd sites above R^2, p<r are odd, and r*b
exceeds both actual sites, then r*b is already at least
(R+1)^2. It cannot cross the physical clock later inside
the same square band. This is an independent product/odd-gap
inequality, not an RH assumption.

The remaining orientations also have direct clipping
interpretations. The finite census is now a concrete
acceptance test for an all-scale native source-classifier
Lean specialization rather than a vague analogy.

## Essential signed counterexample uncovered by variable cutoffs

The signed next-right sector does **NOT** stay negative for
every within-band x. In the consecutive scan R=8..200,
60 roots had temporarily positive next-right clips, although
all their completed blocks had negative next-right totals.
For R=25:
- at x=629, P_x=0, C_x=2 and next-right=+0.099177495;
- the first prime enters at x=631 and next-right turns -0.3323.

For R=166 the signed next-right reaches +0.999756882
at x=27580, just before the first prime arrives at x=27581.

Thus the **static orientation classification** survives this
adversarial scan, but **a universal pointwise restoring
sector sign is empirically FALSE**. The condition
\[
w_RN_x\le(1-w_R)P_xC_x
\]
is equivalent to next-right nonpositivity, and is not
automatically implied by the owner index. It must not be
inserted as an axiom or treated as a consequence of
the existing return pairing.

## Honest remaining theorem

An all-root Lean theorem identifying the actual native
\`vfMidActiveReturnedRawParentFiberMass\` from original
source pairs with the explicit six orientation classifier
(at the completed root, and then the integer-cutoff
continuation) is the next **formalization** target.
The already-proved finite algebra in the Wiles kernel
and the new odd square-band no-intermediate lemma are
not themselves a proof of that entire native identity.

Even after native identification, controlling the entire
historically conditioned signed original Sector Six under
a hypothetical first-bad endpoint remains OPEN and
RH-strength. This census supplies exact finite evidence
and an arithmetic classification, not a quantitative
global cancellation theorem.
