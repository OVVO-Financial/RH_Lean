# Single leaderboard source target: actual retained near-saturated Hecke fibers (2026-10-26)

**Status: OPEN SOURCE THEOREM.** This is an exact-source **proposed mathematical target**, not a proved theorem, not new Lean code, not a certified gain, and not an assertion that the numerical return sensitivity continues after all guards are replayed. Supersedes the *leaderboard allocation* in [the prior two-lane contract](QRH_SOURCE_ESTIMATE_EXECUTION_CONTRACT_20261026.md), not the repo's independent RH research portfolio.

## 1. Certified target and admissible scope

- Tracker merged #76 (all Dirichlet L functions, uniform modulus): β=349843/400000=0.8746075. Proposed #79 (0.8746074) was **OPEN, not merged** at verification; always refresh before using either threshold.
- **Only leaderboard track:** original retained Hecke HIGH near-saturated fiber/cardinality exponent, fixed admissible amplitude strip weightedMean/δ >= 49/100. Budget ν≈3/40000=0.000075 is a **conditional model scenario**, not a verified uniform arithmetic or analytic saving.
- Secondary **same-source** track: improved marked inverse cost μ=2→1.995 (or 1.9) when legitimately proved with all source, guard and return constraints. The imported original source row moment is OAI 7/8; tracker #76 is not currently a native RH_Lean theorem.
- Direct Co/Div with integer μ(n), original square-block covariance, finite-A/C, VF and prime/composite arithmetic remain separate RH mathematics, but do **not** qualify by themselves for the all-Dirichlet leaderboard. Do not spend a leaderboard agent slot on a zeta-only bound. If one seeks an all-Dirichlet extension, it needs a separate theorem uniform in every Dirichlet modulus/character and successful tracker verifier.

## 2. Exact row family; do not substitute an arbitrary finite test

Original checked file prefixes (the exact head SHA must be recorded at every run):

`submissions/arvi-repeated-marks-on-sil-face-20261025/src/Submissions/arvi_repeated_marks_on_sil_face_20261025/`

- `Source/FiberK.lean`: `feedback_fiber_count_K`, `FiberMomentsK`, `classCutoff` and `gainRep`.
- `Source/WeightedK.lean`: `BinLabel`/`binValue`, `adaptiveFiberK`, `adaptiveKeyK` and `weighted_row_sum_K`, including the sum over every bin, label, dyadic pair.
- `Source/ActualWeightedK.lean`: **actual-source quantification** in `ordinary_actual_weighted_row_sum_K`, particularly lines 31–62 and source extraction at 64–68. This imports actual `NaturalBatch`, `UnitFaceSource`, the unmarked supplier, original plain marked supplier, and `replicated_inverse_source_field`.
- `Source/CountWrappersK.lean`: `ordinary_actual_weighted_row_sum_rm`, specializing to 8 repeated marks and exposing the exact high proof interface.
- `FinalReturn/ReturnFormulas.lean`: `countJ`, `countN`, `rowMargin` and the **15 admission guards**; `FinalReturn/ReturnConstants.lean` contains the current rational record. `Gain/Gain.lean` supplies the class-dependent gain and its hard p=1/2 cap.
- `FourthPower/RepairedRestrictedSource.lean` and `FourthPower/RepairedActualSideProvider.lean` are the actual **all-root-family uniform Sil source**, not a numerical alternative to it.

**Do not mistake the row family for all possible independent amplitude vectors.** In the actual theorem, for a fixed legal Eisenstein ideal modulus M, subgroup H and character data `base,anchor,bad`, physical weight W, admitted `DensityCountingSetup`, source face and εm, one has an eventual-in-U statement **for every admissible actual**:

`B : NaturalBatch (Slot:=Slot) M H hH base anchor bad W (33/50) (33/50) U`.

For this B the selected slots and physical complex coefficients are `B.slots`, `B.widths`, `B.Q`, `B.family` and retained rows `B.rows`. Set

```text
delta := 2*a - 1              (1/2 <= delta <= 3/4)
S     := sum(s in B.slots) B.widths(s)
g_bin(s) := binValue B.slots (delta/2) binWidth bin s
q_bin := weightedMean B.slots B.widths g_bin
p_bin := q_bin / delta        (0 <= p_bin <= 1/2 on actual fibers)
t_bin := binCutoffK 8 capacity lam cap B.slots B.widths a binWidth bin
F_bin := adaptiveFiberK 8 capacity lam cap
  B.rows B.slots B.widths B.Q B.family
  U a eps T allowance binWidth i hbin witness
  bin label left right
```

The bin membership and legal witness are *exactly* those in `adaptiveFiberK_fields`; no post-selected frequency, conductor, relative-height, positive weight or masking is discarded. The near-saturated stratum is `49/100 <= p_bin <= 1/2`. It includes the endpoint p=1/2; prove uniformity there, not merely for p<1/2. For empty F the inequality is trivial; the actual theorem must treat all nonempty F.

## 3. Precise uniform theorem that is not currently available

The sought strengthening has the **same outer binders and source hypotheses** as `ordinary_actual_weighted_row_sum_K`, with copies specialized to 8. Write `theta_0` for the present upper exponent of the **individual F_bin cardinality**, before multiplying by squared products. A literal *sufficient candidate* to test is:

```text
For a FIXED nu = 3/40000 > 0 (or any explicit nu>0 sufficient
after complete return) and every fixed permitted original:
  M, H, hH, base, anchor, bad, hbadM, hbad0, hbadTop, hbad72,
  capacity, lam, cap, sourceMesh, hB0, hB1, hlam, hh0, hh1,
  setup, W, bPhi, eps_m>0, zeta>0, hsource, hWs, hW,
  hbPhi, hrad, hBeta:
there exist J:N and C>0, depending only on that fixed source data,
such that eventually for all real U>1:
  for ALL actual NaturalBatch B above;
  for ALL admissible a, eps, T, allowance, mesh, binWidth, height, i
      and all existing Source/ActualWeightedK bounds and physical masks;
  for ALL legal SupportedWitness families (one per bin) and hQ;
  for ALL bins, labels and dyadic left/right (including all conductors):
    if 49/100 <= p_bin:
      (F_bin.card : R)
          <= C*(1+height)^J * U^(E_count(bin) - nu),
where
  E_count(bin) =
    rho(delta) + delta*S
    - gainRep 8 delta capacity lam cap S 1
    - 2*q_bin*S
    + 155*eps + mesh + eps_m + delta*zeta.
```

**This is intentionally only a candidate**, written in the source's variables to expose precisely what has to be proved. The actual `feedback_fiber_count_K` proves the same bound **without** `-nu` under `FiberMomentsK`, and `ordinary_actual_weighted_row_sum_K` gets those moment fields for actual B. The moment step is not an independent uniform saving. If the candidate is FALSE for legitimate actual rows or too strong to prove, the agent must return the smallest admissible counter-family and a weaker **proper-source** replacement that still yields an independently justified positive gain.

**Diagnostic of the existing class slack, not a theorem:** evaluating the six literal `Gain/Gain.lean` facet roots with K=8, B=0.99999, lam=3.72, cap=0.06, Q=1, produces `gainP(delta,1/2)-gainK(delta) = 0` in some legal geometry (for example delta=0.7, S=0.03), but positive gaps in others (for example delta=0.5, S=0.06 gives about 0.000096). This is a *model computation on the existing deterministic geometry*, not a test that an actual source family realizes those parameters. It demonstrates exactly why the uniform improvement must **pay** class-sharp slack and why a global `-nu` against `gainK` can already be a restatement in some bins.

**Crucial anti-false-gain check:** `FiberK.lean`'s count proof first controls the **class-specific** `gainP delta p ...`, and only at the end relaxes it to global `gainK/gainRep` (see `gainP_count_identity` and `gainK_le_gainP`). A claimed ν against `gainRep` that merely recovers `gainP-gainK` is deterministic **old slack**, NOT a new analytic source estimate. Quantify and subtract that existing per-class slack at the near-saturated face; a valid new arithmetic theorem must exceed the locally sharp existing count, or else certify a better full return from an already proved but previously unused class-specific theorem. Do not double-count both.

The actual production proof should yield **bin-local** sharpened cardinality and then reassemble `weighted_row_sum_K` by splitting near-saturated vs. complement. On the complement p<49/100 use the original legal bound and prove the full return is strictly positive for all admissible δ and all 15 `admissionGuard` inequalities, including endpoints and any bin-width/mesh transition losses. Do not simply subtract ν from every term of the full weighted row sum. Repeat all stages of `CountWrappersK`, density, natural count, high/low, Poisson, physical face and final Dirichlet theorem. **The Lean source-bound theorem and the final tracker-verifier certificate are separate acceptance gates.**

## 4. The marked-cost alternative: correction to the earlier "two-copy" worry

The original inverse supplier imposes both `r+2z<1` and `2r+8z<3`. If an independently proved marked-moment theorem changes only the first cost to `r+mu*z<1`, and z is taken as near (1−r)/mu, the **existing** second condition remains feasible for every 23/37<=r<1 provided

```text
mu > 8*(1-r)/(3-2*r) <= 112/65 ~= 1.723076923.
```

Hence μ=1.995 or μ=1.9 is **not obstructed by the second inequality in this admissible range**. At the strict first boundary the z choice still needs positive slack; do not silently replace < with ≤. The actual open issues are a genuine strengthened first inverse-moment theorem, valid local row counting and **all** modified 23/37, 7/37, 15 return/admission guards. The old instruction that the second moment restriction must necessarily be re-proved for μ near 2 was too strong; re-check it, do not claim it is binding.

Sil's physical B0=0.99999 has only 1e−5 admissible headroom before B<=1, buying approximately 7e−8 of modeled θ. **B0>1 is invalid.**

## 5. Allocation / honesty / progress threshold

**Leaderboard research slot allocation**: Analytic #5 proves the proper uniform near-saturation row theorem; Coordinator #1 reconstructs exact per-bin, physical and 15-guard return and certifies the sensitivity once sourced; Referee #3 attacks the true statement and checks class-specific slack and all quantifiers; Lean #7 formalizes source-faithful theorems only when proven; Census #4 checks *actual* retained Hecke rows and smallest counterfamilies (and can maintain separate non-leaderboard arithmetic evidence); Owner #2 and Wheel #6 retain their independent original genuine-prime/VF/CORR4 duties without being misassigned as alleged all-Dirichlet Hecke inputs.

**Pass/fail report:** exact original theorem (source SHA), FIRST missing analytic lemma, eligible actual row family, old class-sharp bound, proved ν or UNKNOWN, complete legal losses/admission guards, updated optimized β and all-Dirichlet proof scope or `NOT_CERTIFIED`. If no new independent source estimate is found, report `NO_UNIFORM_SOURCE_GAIN`. Do not invent a source theorem or change the verifier geometry to manufacture one. Zero accepted additional certainty from an LPM/UPM identity alone.

Existing one run/day per specialist, six own-report-only agents, authorized Lean draft-only branches and **human-only merge** remain unchanged. The updated ledger itself has not been uploaded into this corrective PR; the user-provided corrections and precise source target are mirrored here without silently substituting the superseded ZIP.
