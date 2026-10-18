# RH_Lean agent daily report - 2026-10-17 / RH | Analytic Type II

**Status:** COMPLETED
**Invocation:** scheduled run at 2026-10-17T22:26-04:00
**Canonical objective:** `VFCanonicalSquareVonKochStatement` remains OPEN.
**Result classes:** `PAPER_PROOF` (new shell response projection/inverse theorem), `PAPER_PROOF` (sharp generic block-norm barrier), `FINITE_COMPUTATION` (exact genuine-Mobius projection census), `NO_NEW_BOUND` on the shell exponent, global covariance, canonical VF target and RH.

## A. Most important analytic development

### Claim `20261017-analytic-1` - prime/composite response projection theorem

For integer (H\ge2), let
[
I_r=\{r^2+1,\ldots,r^2+2r\},qquad
Q_r=\#\{p\in I_r:p\text{ prime}\},
]
[
V_r=\sum_{\substack{n\in I_r\\n\text{ composite}}}\mu(n),qquad
\Delta_r=\sum_{n\in I_r}\mu(n)=V_r-Q_r
quad(H\le r<2H).
]
Every prime occurs once with (mu(p)=-1); all composites, including squareful zero terms, remain on the genuine carrier. Put
[
A_H=\sum V_r^2,quad B_H=\sum Q_r^2,quad
X_H=\sum V_rQ_r,quad E_H=\sum\Delta_r^2.
]
For all sufficiently large (H), (B_H>0). Define
[
\lambda_H=X_H/B_H,qquad
R_H=\sum(V_r-\lambda_HQ_r)^2.
]
Then the exact orthogonal decomposition is
[
\boxed{E_H=R_H+(\lambda_H-1)^2B_H.}\tag{P}
]
Indeed (sum Q_r(V_r-lambda_HQ_r)=0), so the cross term vanishes. Thus the shell problem separates into two genuinely independent obligations:

1. **shape residual:** (R_H), the composite response after removing its best scalar prime-shell mode;
2. **scalar calibration:** ((X_H-B_H)^2/B_H), forcing the response coefficient to be (1), not merely some coherent multiple.

Neither obligation alone suffices. The synthetic coherent mode (V=2Q) has (R_H=0) but (E_H=B_H); any arbitrarily large vector orthogonal to (Q) can have (lambda_H=1) but large (R_H). These are ambient-vector falsifiers, not claimed Möbius counterexamples.

The PNT and Cauchy--Schwarz give
[
\sum_{H\le r<2H}Q_r
=\pi(4H^2)-\pi(H^2)\sim\frac{3H^2}{2\log H},
]
hence, for an absolute (c>0) and all sufficiently large (H),
[
B_H\ge c\frac{H^3}{(\log H)^2}.
]
Trivially (A_H,B_H\le16H^3).

Consequently, if for fixed (kappa\ge0), every (eta>0), and all large (H),
[
E_H\le K_\eta H^{5/2-\kappa+\eta},\tag{S}
]
then
[
R_H\le K_\eta H^{5/2-\kappa+\eta},
]
[
|\lambda_H-1|
\le C_\eta H^{-1/4-\kappa/2+\eta/2}\log H,\tag{C}
]
and the genuine signed mixed moment must satisfy
[
|X_H-B_H|
=\left|\sum Q_r\Delta_r\right|
\le 4\sqrt{K_\eta},
 H^{11/4-\kappa/2+\eta/2}.\tag{M}
]
Also
[
|A_H-B_H|\le
8\sqrt{K_\eta},H^{11/4-\kappa/2+\eta/2}.
]
Conversely, (R_H\ll_\eta H^{5/2-\kappa+\eta}) together with
[
|\lambda_H-1|\ll_\eta
H^{-1/4-\kappa/2+\eta/2}
]
implies (S), using (B_H\le16H^3). This is a strict two-part sufficient program: residual control permits a wrong coherent scalar response, while calibration permits arbitrarily large orthogonal noise.

Define the dyadic two-population Gram
[
\rho_H=\frac{2X_H}{A_H+B_H}.
]
Then
[
1-\rho_H=\frac{E_H}{A_H+B_H},
]
so (S) forces
[
0\le1-\rho_H\ll_\eta
H^{-1/2-\kappa+\eta}(\log H)^2.\tag{R}
]
This is a **necessary inverse conclusion**, not a newly proved rate for genuine Möbius data. It is distinct from the repository's root/smooth (ho_R), which has different signs and carrier.

**Status:** `PAPER_PROOF / NEW INVERSE THEOREM / NO_NEW_BOUND`.

**Quantitative payoff if independently paid:** (kappa=0) supplies the open shell (7/8) benchmark; any fixed (kappa>0) improves the Mertens exponent to (7/8-kappa/4), as in the existing square-clock argument. The theorem itself does not establish either input.

## B. Why this is the right mixed moment

The newly merged #973 stop test shows that subtracting prime-only coherence without its mixed bill is invalid: (sum Q_r^2\gg H^3/\log^2H), larger than the (H^{5/2+eta}) shell budget. Formula (P) states the exact bill. The desired cancellation is not “primes cancel composites” informally; it requires both:

[
\sum Q_rV_r=B_H+O\bigl(H^{11/4-\kappa/2+eta}\bigr)
]
and a power-bounded response component perpendicular to (Q).

This formulation retains all nonprime Möbius signs before taking a norm and gives an inverse theorem: excessive shell energy is caused either by a coherent response miscalibration or by a large orthogonal composite mode. It also explains why a near-one scalar correlation without denominator control is insufficient.

The first independently missing estimates are precisely:

[
R_H\ll_\eta H^{5/2-\kappa+eta}
quad\text{and}\quad
|X_H-B_H|\ll_\eta H^{11/4-\kappa/2+eta/2}.
]
They must be proved from prime/composite or unshared-prime arithmetic. Their conjunction is equivalent to the shell target through (P), so neither should be relabeled as already easier merely because it is projected.

## C. Claim `20261017-analytic-2` - sharp generic block-norm barrier

For arbitrary coefficients (a_n) on the disjoint shells (I_r),
[
\sum_{H\le r<2H}\left|\sum_{n\in I_r}a_n\right|^2
\le(4H-2)\sum_{n\in\cup I_r}|a_n|^2.\tag{B}
]
This is Cauchy--Schwarz on each shell. The operator constant is sharp for the ambient coefficient class: support (a) constantly on a longest shell and zero elsewhere. Since the union contains (H(3H-1)) sites and (|\mu(n)|\le1), (B) gives only (<12H^3).

Therefore disjointness, coefficient boundedness, squarefree density, or an unstructured Hilbert/large-sieve norm cannot reach (H^{5/2-kappa+eta}). A proof needs an arithmetic saving of (H^{1/2+kappa-eta}) in the complete signed response. This does not rule out a genuine Möbius dispersion theorem; it identifies the exact structure that theorem must use.

**Status:** `PAPER_PROOF / SHARP AMBIENT NO-GO`.

## D. Claim `20261017-analytic-3` - exact finite projection census

A fresh linear Möbius sieve computed (A_H,B_H,X_H,E_H) with integers for every shell in each dyadic range through (H=2048). It checked (E_H=A_H+B_H-2X_H) exactly.

| H | (A_H) | (B_H) | (X_H) | (E_H) | (lambda_H) | (E_H/H^{5/2}) |
|---:|---:|---:|---:|---:|---:|---:|
| 256 | 1,172,686 | 1,090,186 | 1,076,328 | 110,216 | 0.987288408 | 0.10511017 |
| 512 | 7,440,330 | 7,008,021 | 6,980,708 | 486,935 | 0.996102609 | 0.08209110 |
| 1024 | 47,362,993 | 46,012,166 | 45,825,886 | 1,723,387 | 0.995951506 | 0.05136093 |
| 2048 | 313,311,253 | 307,337,568 | 306,634,203 | 7,380,415 | 0.997711425 | 0.03888265 |

At (H=2048),
[
R_H/H^{5/2}=0.03887417,qquad
(\lambda_H-1)^2B_H/H^{5/2}=8.48049\times10^{-6}.
]
Thus the orthogonal residual dominates the scalar miscalibration in this finite range. This discriminates the next experiment: test a phase-bearing estimate on the residual, rather than spending the next run only refining the already-small scalar coefficient. No power law is inferred.

Scratch source SHA-256: `90db5897cb17023a5db4579416de868e0a809a8c7912ccfa0e226005a9e039f9`.
Output digest: `6b06b446d91b4d0e78ca8abf1d46224b8364d8f8aabb79f6a56c10f1817d4dce`.
Compiler command used `g++ -O3 -std=c++17 -Wall -Wextra -Werror`. Floating values are display-only; all defining moments and the identity check used 64-bit integers, whose largest observed magnitude was below (3.2\times10^8).

**Status:** `FINITE_COMPUTATION`.

## E. Authority, continuity and source evidence

- New York report date: 2026-10-17.
- Actual main HEAD at final refresh: `5aa5eb28c352882b8c8cd8d3e0714ddc5afcc555`, merge of #973.
- Authority blobs: `AGENTS.md` `aef9d6f7a7d3a091f947effd38e9ad42a63e8445`; `CURRENT_PROOF_CONTRACT.md` `873ec6f70525e1e9ba1defecf8b0951ebe155069`; signed-covariance directive `8d846d6ee5d559065687b2ed5144aeb7ca3e1850`.
- Main source blobs: weighted covariance `277b3f209788077b66fa6095d7c1358897b94e91`; deterministic Green--Kubo `172e0323f7804c08f7c4e77f2a7bc1af4c6cbd0d`; shell-energy note `8c881169efccd3eaf129af4321a1c4becb3833bf`; shell compensation note `d7826257273473e80948117ea5c0fcd04713af6f`; shell compensation Lean `3bf26af6f058d2057acc99c911fa11cb9a73c796`.
- PR #968 is merged into main (merge `c43284955c8272e6211df7b47876c92cb178810a`); all eleven workflows on proof head `4f88a1d2b88c3ee4a34b0619a114167d0218a964` succeeded.
- PR #969 is marked merged only into the stacked feature branch; its OAI source is absent from main. Status: `PROVED_IN_LEAN_ON_NONMAIN_BRANCH / INTEGRATION_REQUIRED`, not on-main authority. Its five head workflows succeeded.
- PR #973 is merged into main. All twelve workflows on exact proof head `475b6014df268620486b82add85d4757c06829a4` completed successfully, including the dedicated shell certificate, Lean build/axiom audit, source audits and proof inventory.
- Open PR search at intake: none.
- Today upstream blobs consumed: Coordinator `9a797b07dcd7c74147b6b0cdbc8f6a69024c3961`; Owner `6980422de5f7cc55b9dec32a2f0fe21f98ed7ff1`; Wheel `dbaefd4005c2cc93b894f9bb97c7a74c5f28dc49`; Census `9efa34cd7a2d3c021b20779889eaaf6a556020d3`; Referee `a3867e19b4e6e409c09ab69899a628d042f11a8d`; Lean `1a03815f26aa6ee145d94c9848ac37483b093033`.
- Complete October 16 set consumed as `YESTERDAY=CARRY_FORWARD`: Coordinator `fc5c5b46a0ec56f606444bb5dbfe400d4a444d18`; Owner `cb42efd7a6aa0e782c353803e604684b9500cdb2`; Analytic `2b93e7c237c09439746a93356c20cd15e4671028`; Wheel `134eb9eb0558a622b6f042baa20f3feb847ed6f4`; Census `26510606eea9f43450e5bb092c4542ab23fcb729`; Referee `e4c0a92301f032eb732a51f7bd997f4a19ac8b48`; Lean `180cf24f8444852a5b69bf2581f0c6d160f3a16e`.
- External inbox blob `3cd80e68cec54cc9ce1e00a384cfe37a3a3babc0`; `EXT-20261017-XCOORD-1..3` and `EXT-20261017-HECKE-1..3` consumed at their stated exact/open scopes.

## F. Complete-source and no-circularity audit

- Genuine Möbius coefficients: **PRESERVED**.
- Strict square shells and all endpoints: **PRESERVED**.
- Prime occurrences: **PRESERVED ONCE** through (Q_r).
- Composite signs and squareful zeros: **PRESERVED** through (V_r).
- Diagonal, prime-prime, prime-composite and composite-composite terms: **PRESERVED** in (P).
- Uniformity: theorem statements are all dyadic (H); constants may depend on (eta), not on (H).
- External OAI (7/8): **NOT USED** in the proof or census.
- Original VF weights, #915 masks/clips, returned-cell admission, anchors and restoration: **NOT_APPLICABLE / NO BRIDGE CLAIMED**. This is the stronger unweighted square-shell route.
- Global (C(N)) and weighted (C_\varepsilon(T)): **NO DIRECT BOUND CLAIMED**. The route to them is through a newly paid shell estimate and the existing square-clock/Mertens consumer.
- The projection identity is not a bound. The two proposed inputs jointly reconstruct the target and are not credited as independent progress until one is proved from new arithmetic.

## G. Mechanism decision and handoff

**Decision:** `CONTINUE / REVISE` the shell mechanism. Suspend any second centering that merely recombines all divisor bands or deletes (Q_r^2). Use the response projection (P) as the falsification interface.

**Next independent analytic question:** can the exact gcd/unshared-prime expansion prove a power-saving dispersion estimate for the orthogonal residual
[
\min_{\theta\in\mathbb R}
\sum_{H\le r<2H}(V_r-\theta Q_r)^2
]
without assuming a bound on (sum\Delta_r^2), while a separate prime-weighted summation controls (sum Q_r\Delta_r)? A valid theorem must keep all (r), square endpoints, repeated/shared factors, and the full composite response.

**Handoffs:**

- Coordinator: treat residual and calibration as two separately falsifiable arrows, not two achieved bounds.
- Owner/Wheel: express (R_H) occurrencewise in the established gcd/unshared-prime partition; do not drop the (c=1) channel.
- Census: pre-register held-out (H>4096) and record (R_H/H^{5/2}), calibration/H(^{5/2}), (lambda_H), and worst-window spikes.
- Referee: audit (P), the PNT denominator, exponent arithmetic and the two ambient countermodels.
- Lean: only after review, the finite projection identity is a clean generic inner-product lemma; it must not be presented as the missing quantitative estimate.

## H. Final summary and resume capsule

New claim `20261017-analytic-1` gives the exact prime/composite projection and the quantified inverse restrictions (C), (M), and (R). Claim `20261017-analytic-2` proves that generic block norms stop sharply at (H^3). Claim `20261017-analytic-3` finds that the orthogonal residual, not scalar miscalibration, dominates the genuine finite shell energy through (H=2048).

No independent (kappa>0), no (kappa=0) shell theorem, no below-(3/8) weighted covariance bound, no improved Mertens exponent, no canonical VF estimate and no RH proof were obtained.
