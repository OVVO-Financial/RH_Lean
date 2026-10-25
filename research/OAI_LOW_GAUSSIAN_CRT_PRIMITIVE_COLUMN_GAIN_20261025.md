# Original OAI low-Gaussian: primitive s*I CRT improvement
Date: 2026-10-25. Extends PR #1022 without replacing its certified theorems.
Original source: openai/math@1581d4cbdd69a0faf34b2089614fe2a814316a6a.

**Status: source-local mathematical argument, not yet an imported Lean analytic theorem and not a global exponent improvement.** These statements concern each FIXED, admitted original completed-source (s,I,J) m-summand before outer source/compensation costs. This note is not a proof of any new Mertens exponent or RH.

## 1. Precise hypotheses and characters

Work in O=Z[omega]. Let s be a good prime ideal of norm q comparable to Y=Z^(23/48), and I an admitted good squarefree column ideal. Assume the original calibration generator g is coprime to s*I*J; the true completedMask and correction are retained. In the nonresonant sector assume s does not divide I*J. Original completed-source numerator is

  rho_C(m) * conj(chi_s(m)) * chi_I(m) * chi_J(m)^3

with zeros at the original nonunits, and Q_s = N(g)*q*X, X=Z^(17/48). All other factors in the fixed (s,I,J) summand are independent of m. The frequency-zero cancellation for this original source is certified in PR #1022, as is periodicity modulo (g)*s*rad(IJ).

For each prime p|I, the residual sextic exponent is 1+3*v_p(J). Since I is squarefree, this exponent is 1 mod 6 when v_p(J) is even, and 4 mod 6 when v_p(J) is odd. It is NEVER 0 mod 6. The exponent at s is -1 mod 6. Provided the good-prime sextic characters really have order 6 (ramified/characteristic-2 primes are excluded), EVERY prime of s*I therefore carries a nonprincipal primitive local character.

Set G = s*I and H = (g) * product_{p|J, p not dividing I} p, so G and H are coprime under the assumptions. On O/(G*H) the original m-character is a CRT product chi_G*chi_H, with chi_G primitive at every prime of G and |chi_H| <= 1 on every residue (including the original zero masks). The possibly imprimitive factors of J outside I, and calibration, are kept in H: they have NOT been deleted.

## 2. Finite Fourier/Gauss theorem and bound, independent of Q

Let g0=N(G)=q*N(I), h0=N(H), F=g0*h0. Finite CRT factorization of the additive Fourier transform, with invertible frequency-coordinate scalings, gives

  |hat(chi_{G*H})(xi)| = |hat(chi_G)(xi_G)| * |hat(chi_H)(xi_H)|
                        <= sqrt(g0) * h0.

The first factor is exactly bounded by sqrt(g0): each local nonprincipal primitive sextic power has a prime Gauss sum of magnitude sqrt(N(p)), and the CRT product multiplies these magnitudes. At the zero frequency hat(chi_G)(0)=0, so hat(chi_{G*H})(0)=0.

For a fixed compactly supported smooth radial W define

  S(Q) = sum_{m in O} chi_{G*H}(m) W(N(m)/Q).

Period-lattice Poisson for the ideal G*H gives, up to the fixed Eisenstein covolume/dual-lattice factors,

  S(Q) = (Q/F)*sum_{xi in a fixed dual lattice} hat(chi_{G*H})(xi)
                                      * Vhat(sqrt(Q/F)*xi),

where V(z)=W(|z|^2), and the zero term vanishes. Since V is Schwartz in two real dimensions,

  sum_{xi != 0} |Vhat(r*xi)| <= C_W * r^(-2)  for every r>0.

The bound is uniform in the modulus and Q: for r<=1 use lattice point counting and rapid decay; for r>=1 use decay of order k>2. Therefore

  |S(Q)| <= C_W * h0*sqrt(g0)

for EVERY Q>0, not merely F<Q. This is a full-period incomplete-character estimate (a smooth 2D Polya-Vinogradov-style bound), not statistical independence, covariance, or a Poisson period-smallness assumption.

For the original normalization, h0 <= N(g)*N(rad J) and Q_s=N(g)*q*X. Hence

  |S(Q_s)|/Q_s <= C_W * N(rad J)*sqrt(N(I))/(X*sqrt(q)).

If N(I)*N(J)^3 <= Z^(1+1/384) in the stated Gaussian bulk, write
t=log_Z N(J), d(J)=log_Z(N(J)/N(rad J)) >=0. Then

  |S(Q_s)|/Q_s <<_W Z^(-71/768 - t/2 - d(J)).

Proof of rational exponent:
  (1+1/384)/2 - 17/48 - 23/96 = -71/768.

Thus every admitted fixed s-nonresonant term satisfying these hypotheses has at least Z^(-71/768) normalized m-sum saving, even at small t. For t>67/384, s cannot divide I by the Gaussian size bound, and N(J)<N(s), so all admitted terms in that t-region are covered. For lower t, separate s|I from s not dividing I. The weaker s-only bound gives the previously identified threshold t>157/768; extracting the additional good I-primes removes that threshold for the fixed subsource.

## 3. The true resonant exception

When s|I and s does not divide J, the local exponent at s is -1+1=0 mod 6: the original phase cancellation of #1011 is real. The m-factor can have a PRINCIPAL zero/nonunit mask at s and a nonzero zero Fourier mode. No application of the nonprincipal Gauss theorem to that factor is legitimate.

Writing I=s*I' in that sector does introduce the exact column normalization 1/sqrt(q*N(I')), but a complete detector bound must include the I' source count, all q sums, Gaussian profiles, the other primitive factors, ray terms and the original compensated source. There is no proof here that the full resonant energy is power-small.

## 4. Corrected squarefull Rankin calculation (independent useful sublemma)

Factor J=J_sf*M with J_sf squarefree, M squarefull and coprime to J_sf. Define D=M/rad(M). Then M=D*rad(D) uniquely, and
  N(J)/N(rad J)=N(D).
Therefore, for fixed B,d0>0 and any 0<epsilon<1,

  sum_{N(J)<=Z^B, N(D)>=Z^d0} 1/N(J)
    <= [sum_{N(S)<=Z^B}1/N(S)]
       * sum_{N(D)>=Z^d0}1/(N(D)*N(rad D))
    <<_epsilon (1+log Z) Z^(-(1-epsilon)*d0).

The convergent Euler product for Rankin is
  sum_D 1/(N(D)^epsilon*N(rad D))
    = product_p (1 + 1/[N(p)*(N(p)^epsilon-1)]) < infinity
for every epsilon>0, using ideal-prime summability above 1. Consequently, at any fixed d0>0, the high-deficiency harmonic mass is in fact O(Z^(-d0+eta)) for every eta>0 (the logarithm is absorbed), stronger than the originally proposed O(Z^(-d0/2+eta)). This by itself is only a J-weighted tail, not full-source energy.

## 5. Original theorem locations and acceptance gate

Source definitions: Detector/PhysicalRows.lean, Detector/Completed.lean, Arithmetic/IdealMobius.lean.
Existing Lean inputs: Detector/PhysicalCRT.lean::coprime_function_fourier;
CubicSieve/Poisson.lean::norm_canonicalGaussSum_of_nontrivial;
CubicSieve/Poisson.lean::canonical_finite_prime_gauss_transform_scalar_of_nontrivial;
Detector/Sextic.lean::actualSextic_pow_eq_one_iff;
Detector/PhysicalReopen.lean::physical_spectral_reopen.
PR #1022: VF919OriginalLowNonresonantZeroMode.lean and VF919OriginalLowRadicalPhysicalPeriod.lean.

The next Lean adapter must (1) prove the source-exact local 1+3*v_p(J) exponent and good-prime partition of s*I vs H; (2) transport the exact calibrated masks through CRT; (3) use the existing primitive Gauss theorem with the trivial bound on H; (4) implement the uniform nonzero-frequency radial Fourier lattice sum, preserving Q_s and original gaussian and row normalizations. It must then sum ALL labeled I,J,s, ray and compensation modes, keep the external original high-row and multiplicity/moment gates, and independently establish a better global detector exponent.

Neither this paper argument nor the finite probe proves that last full-source theorem. The small-prime/numeric probe is only a CRT norm sanity check: scripts/oai_low_gaussian_crt_good_column_probe.py.
