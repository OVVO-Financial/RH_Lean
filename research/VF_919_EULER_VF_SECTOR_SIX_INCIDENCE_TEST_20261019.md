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
