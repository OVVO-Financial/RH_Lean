# Heavy-slot resonance: corrected minimal-power-saving gate

Research audit, 2026-10-25. This does not establish a new Mertens
exponent, Gaussian moment, or the Riemann hypothesis.

## I. Coprime heavy-slot toggle preserves the exact original resonance

The certified theorem in
research/oai_434/VF919OriginalLowGaussActualResonance.lean
(actualLowGauss_inverseRowTwist_exact_resonance) states for an
admitted supported prime ideal s and b,m coprime to s:

 G_s(-m) * rowTwist(Psi,b,1,m,s) = G_s(-1) * Psi(s).

This conclusion holds for EVERY coprime b. Thus if an adjoined prime
slot p leaves bp coprime to s, precisely the same m-INDEPENDENT
resonance persists after b is replaced by bp. The rowTwist includes
b^6, whose sextic character is 1 on this coprime branch.

If p divides s, the original theorem's coprimality premise fails:
that is an exceptional/mask/collision sector, not automatically a
nonprincipal character sum. The actual 3/4/12-style restoring and
principal source bills cannot be discarded.

The original #1017 source file
research/oai_434/VF919OriginalFiberHeavySlotSplit.lean
proves a fixed slot of width at least 7/(37 #slots) and an exact
finite powerset split. It proves no lower bound on the proportion
of the ORIGINAL weighted row energy carried by this slot.

## II. Small cross energy alone cannot lower a growth exponent

For two source channels F0,F1 in the original weighted row space,
set D=||F0||_omega^2+||F1||_omega^2 and
C=Re <F0,F1>_omega. The EXACT total energy is

 E = ||F0+F1||_omega^2 = D + 2C.

For a desired target T_beta, the NECESSARY AND SUFFICIENT condition
on this cross term, once D is known, is

 C <= (T_beta-D)/2.

The proposed C=O(Z^(-eta) sqrt(E0 E1)) does not imply total
energy shrinkage. Counterexample: F0=1 and F1=i on a single
unit-weight row gives C=0 but E=2. Near-orthogonality leaves
energy approximately D, not zero.

To save a power one needs either:
  (A) a source-proved power saving on the complete D together with
      a non-adverse cross bound; or
  (B) sufficient NEGATIVE cross correlation to cancel the
      unsaved diagonal, C <= -D/2 + O(T_beta).

A fixed one-slot constant-factor energy improvement does not imply
a Z^(-eta) power saving. Iteration would require proved repeated
source admission, normalization and a sum of effective gains on the
order of log Z.

## III. The two local savings are from DIFFERENT sources

research/oai_434/VF919OriginalVariableExponentThreeQuarters.lean
proves the pointwise original HIGH FreeRow local compensated estimate

  norm(continuedCompensatedLocal + correction*conj(v))
      <= 720 Q^(-3/4)

under its genuine supported/coprime/source contour conditions. It
is NOT a full LOW Gaussian inverse-theta energy theorem. For Q>1,
Q^(-3/4) is numerically LARGER than Q^(-7/8): the advantage is a
more aggressive contour a=3/4, not stronger fixed-Q decay.

research/OAI_ORIGINAL_LOW_GAUSS_PRIMITIVE_PERIOD_COMPLETION_20261022.md
gives the actual period-cell bound O(sqrt(qQ)+q) for a nonprincipal
sextic character times a smooth RADIAL coefficient; with
Q~Z^(5/6), q~Z^(23/48) this has relative Z^(-17/96) gain.
But the ORIGINAL low B(sigma,m)=correctedCompletedT varies with m,
the Hecke conductor, inverse-theta coefficient, Poisson terms and
masks. Taking a coefficient proportional to conjugate(chi_s(m))
cancels the phase and defeats radial saving; the original #1011
rowTwist identity exhibits this resonance explicitly.

No unconditional lift via Vaughan's identity to Z^(-17/288)
has been proved for the full source-specific Type I/II cofactor,
principal, collision and weighted-row bills.

## IV. Exact new theorem that would move the global exponent

Fix the actual original OAI Gaussian source and a heavy slot with
all row, s, b, m, Mellin t, window and compensation labels.
CLASSIFY the paired source atoms after multiplying ALL
Gauss and rowTwist factors:
  (1) persistent coprime resonant modes;
  (2) genuinely nonprincipal surviving characters;
  (3) non-coprime/ramified/principal/collision modes.
Do not infer class (2) just from a conductor change.

Then prove an INDEPENDENT source-level estimate of
D_Z+2 C_Z at the intended detector power. In the normalization
used by the current original high-row contract, the beta target is

  T_beta(Z)= Z^(2(beta-11/16-sigma))
             * sum_u omega_u B_u^2.

For beta=7/8-delta, the exponent is
  3/8 - 2sigma - 2delta.
Prove source admission and pay all OTHER original detector gates
before inferring any Mertens bound. A saving in one restricted
cross sector with unsaved diagonals is not enough.

Alternatively, to use the already certified #1021 q^2 CORR4
contraction, prove on the COMPLETE physical remainder
  |B_R|^2 <= (9/4)E_low(R) + A_delta R^(7/2-4delta)
for all sufficiently large R. The actual all-integer power
bootstrap then converts this to exponent 7/8-delta once its
Lean induction is certified.

No new exponent is claimed here. Next productive step is
an original-source nonresonant classification with the EXACT
inverse-theta, mask, coefficient and source-normalization terms,
followed by an independent quantitative full-energy inequality.
