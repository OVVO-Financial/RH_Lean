# PR #919 — OpenAI 7/8 spectral experiment, conditional in RH_Lean

**Status:** warning-fatal Lean finite Abel/Mellin proofs and conditional
actual-prime/VF endpoint transfer. NOT a kernel-proved import of the
external zeta nonvanishing theorem into RH_Lean. NOT RH.

**External mathematical status as of October 9, 2026:**
Before October 2026, a fixed zero-free half-plane Re(s)>7/8 for
the Riemann zeta function was an open problem. OpenAI released a
September 30, 2026 preprint **claiming a solution**, with a
Lean 4.34.1 proof of the exact theorem

    OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re

in its source module:

https://github.com/openai/math/blob/main/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean

OpenAI's formalization scope note:

https://github.com/openai/math/blob/main/lean/docs/003.md

An independent project reports rebuilding the relevant 2,924
imported Lean modules, with zero errors and only standard
propext/Classical.choice/Quot.sound axioms, on October 7:

https://github.com/tomoto0/quasi-riemann-hypothesis-7-8-verification

This is stronger evidence than an unreviewed preprint alone.
The result is newly claimed and independently *recompiled*, not
a formerly settled classical theorem or yet a broadly reviewed
journal result. Importantly, RH_Lean has NOT itself compiled
OpenAI's external source.

## Separate formal hypotheses

The repository's Lean 4.24.0 toolchain differs from OpenAI's
Lean 4.34.1 toolchain. Hence the external solution has NOT
been imported as a dependency into the native kernel.

The new module
research/VF_MID_SEVEN_EIGHTHS_ANALYTIC_BRIDGE.lean
defines the following explicit propositions:

1. VFMidSevenEighthsZetaZeroFree — the *statement*
   that zeta has no zeros with real part >7/8. This is
   a named proposition, NOT a locally proved theorem.
2. VFMidSevenEighthsPrimeLiEndpointBounded — an actual
   prime-counting estimate at all square endpoints:
   |pi(R²)-Li_2(R²)| <= C R^(7/4) log R.
3. VFMidSevenEighthsExplicitFormulaBridge — the still
   UNPROVED quantitative analytic step (1) implies (2).
   That is not contained in the external zero-free
   theorem statement.
4. VFMidSevenEighthsVFEndpointBounded — a bound on the
   GENUINE actual-prime VF defect at square endpoints.

The actual proved Lean theorem is the conditional implication

\[
\boxed{
|\pi(R^2)-\operatorname{Li}_2(R^2)|\le C R^{7/4}\log R
\;\Longrightarrow\;
|D_R|\le\left(C+\frac{Q}{\log2}\right) R^{7/4}\log R,
}\tag{1}
\]

where Q is the *already kernel-proved* uniform midpoint
Li/VF square-endpoint quadrature constant. Proof:
triangle inequality and log(2)<=R^(7/4)log R
for every R>=2. No fantasy series, no original
Sector Six payment claim, no new axioms.

The proof declarations are
vfMidSevenEighthsVFEndpointBounded_of_primeLi and
vfMidSevenEighthsVFEndpointBounded_of_zeroFree;
the latter explicitly requires BOTH the zero-free
hypothesis and the missing explicit-formula bridge.

## Bidirectional owner/Mellin findings

research/VF_MID_SEVEN_EIGHTHS_OWNER_ABEL.lean proves
exact **genuine prime-counting** error transport
through the original weights on the rank-two p*q
owner graph. It is a finite signed Abel identity,
not a per-owner cancellation estimate.

research/VF_MID_SEVEN_EIGHTHS_MELLIN_SQUARE_KERNEL.lean
proves an exact complex-valued Abel telescope for
the ORIGINAL completed-square VF weight kernel.
Its w_B is an AUXILIARY endpoint, not a physical
new block.

Independent genuine-prime regression:
scripts/vf_919_prime_owner_abel_spectral_probe.py.
At A=2634,B=5267, the 316 owner columns have
125,272 genuine semiprime sites. The signed
original-weight pi-minus-Li model error is
-136.293692; the sum of absolute p-column
errors is 140.783735. Only 1.032944x
cross-column cancellation occurs (293 negative
columns, 23 positive). This directly warns that
completed-square wheel-phase cancellation does NOT
imply analytically centered owner cancellation.

## Open analytic target (not claimed in Lean)

See the complete technical and epistemic contract:

research/VF_MID_919_OPEN_UNIFORM_ANALYTIC_TARGET.md

Specifically:

- Keep the physically truncated pq<B² packet SEPARATE
  from the unrestricted prime-zeta-square Dirichlet series.
- Justify Perron inversion including truncation,
  non-absolute convergence and endpoint conventions.
- Handle the moving A cutoff and logarithm-squared
  singularity at s=1; the claimed ZF78 theorem alone
  supplies no uniform squared-prime moment bound.
- Prove a signed moving-cutoff bilinear estimate strong
  enough to dominate the per-owner absolute errors.
- Reassemble *all* original signed Sector Six Gram
  self and cross terms, once-charging historical owners.

**None of those analytic or RH-strength targets is
established merely by writing the Mellin representation.**

## Reproducing the local Lean bridge

On the pinned RH_Lean Lean 4.24 checkout:

    lake env lean -DwarningAsError=true \
      -o .lake/build/lib/lean/research.VF_MID_VON_KOCH_BRIDGE.olean \
      research/VF_MID_VON_KOCH_BRIDGE.lean

    lake env lean -DwarningAsError=true \
      -o .lake/build/lib/lean/research.VF_MID_LI_UNIFORM_QUADRATURE.olean \
      research/VF_MID_LI_UNIFORM_QUADRATURE.lean

    lake env lean -DwarningAsError=true \
      -o .lake/build/lib/lean/research.VF_MID_SEVEN_EIGHTHS_ANALYTIC_BRIDGE.olean \
      research/VF_MID_SEVEN_EIGHTHS_ANALYTIC_BRIDGE.lean

The PR's dedicated GitHub Actions workflow also checks the
owner Abel and complex Mellin kernel, axiom lists,
upstream source provenance and numerical regressions.
