# J=1 metaplectic residue closure: source audit, algebraic falsifiers and proof gate

2026-10-25. PR #1022. Pinned OpenAI original: openai/math@1581d4cbdd69a0faf34b2089614fe2a814316a6a.

**Status: SOURCE-GROUNDED AUDIT AND ALGEBRAIC FALSIFIERS. No source-wide analytic inequality, no \(7/8-\delta\).** This records the results of the proposed Step 3 and Step 4 pole/exceptional-frequency test; unproved ray-class conclusions are not asserted.

## A. The exceptional modulus is not fixed by calibration alone

Detector/GramClassification.lean defines
\[
G_C=\mathrm{exceptionalModulus}(S,C)=\mathrm{jointFixedModulus}(S)\,C
\]
and ExceptionalFrequency requires \(v_{\mathfrak p}(k)\equiv0\pmod6\) only outside the prime support of \(G_C\). The joint fixed modulus is already larger than the bare calibration ideal (GramJointFixed.lean), and the common ideal \(C\) VARIES.

Since the Eisenstein integer ring is a PID, every exceptional ideal \((k)\) admits a factorization \((u_C)(\beta)^6\) with sixth-power-free \(u_C\) supported on primes of \(G_C\). There are at most \(6^{\omega(G_C)}\) possible ideals \(u_C\) at FIXED C, rather than a universal finite set supported on the calibration ideal. Generators and units require separate ray conventions.

**Small counterexample**: take a good prime ideal \(\mathfrak p\) dividing variable C but not jointFixedModulus(S), and \(k\) generating \(\mathfrak p\). It is exceptional relative to \(G_C\), but would be classified nonexceptional using only the fixed g. The completed ideal J=1 does NOT remove this dependency from the post-Cauchy Gram, because lowSeparatedIntegrand_cauchy has already discarded the completed-source phase.

## B. The signed Mobius divisor acts on primal columns, not on the dual sixth root

Detector/GramCanonicalSource.lean::originalCommonBlock_eq_lattice proves the exact identity
\[
\mathrm{originalCommonBlock}(S,C,k)=\sum_{d\in\mathrm{divisorPool}}
 \mu(d)\,\mathrm{canonicalLatticeBlock}(S,C,k,d,T,Y/[N(C)N(d)]).
\]
Detector/GramCanonicalBlock.lean defines the block as the TWO-variable lattice sum of
\[
\mathrm{canonicalJoint}(S,C,k,d m_1,d m_2)\,
\mathrm{shellProfile}(W,v,U,T,N(m_1)/N,N(m_2)/N).
\]
Thus \(d\) multiplies both PRIMAL variables and shrinks their norm scale \(N=Y/(N(C)N(d))\). It is not constrained by \(d\mid\beta\). This is the coprimality inclusion-exclusion
\[
\sum_{d\mid I,\ d\mid J}\mu(d)=\mathbf1_{\gcd(I,J)=1}.
\]
For \(\beta=7\), primal columns 5 and 11 give d-sum 1, not zero; for \(\beta=1\), primal columns 2 and 2 give d-sum 0, not one. One may ONLY replace it by \(\sum_{d\mid\beta}\mu(d)\) after proving a new and specific divisor incidence theorem.

In GramIdealMass.lean::canonical_exceptional_ideal_sum, the proved bound after k-sum has the shape
\[
\frac Q{Y^3}\left\|\sum_{k\in E_{C,D}}\mathrm{canonicalLatticeBlock}(\cdots)\right\|
 \ll \frac QY\,(N C)^{-7/6+\varepsilon}(N D)^{-2}P^{1/6}.
\]
Here the \(N(D)^{-2}\) is a TWO-dimensional primal-lattice UPPER MAJORANT, not an asymptotic term. No source theorem identifies a d exponent \(1+\gamma/6\), \(\gamma\in\{0,1,2\}\), for a beta-frequency cutoff. The individual canonicalLatticeBlocks are complex-valued, so the exceptional character being principal on \(\beta^6\) does not prove their positivity or an \(\Omega((Q/Y)P^{1/6})\) lower bound. The zeta-factor model is conditional on an unproved separable, nonzero leading profile.

## C. Exact J=1 completed normalization shifts the Dirichlet pole

Here J=1 is the COMPLETED IDEAL J, distinct from the selected-slot subset also named J in LowCentralTuple. Arithmetic/IdealMobius.lean gives exactly
\[
\mathrm{summand}(\Psi,W,T,I,1)
 =\frac{\mathrm{columnWeight}(\Psi,I)}{\sqrt{N I}}\,
  V^\ast W(NI/T).
\]
For the ACTUAL compensated Gaussian fixed window (Detector/GaussianSeminorm.lean),
\[
 W(y)=\mathrm{gaussianAnnulus}(y)/\sqrt y,\quad
 V^\ast W(y)=\mathrm{gaussianAnnulus}(y).
\]
Consequently the J=1 column is \(\mathrm{columnWeight}(\Psi,I)/\sqrt{NI}\) times the annular weight and an additional unimodular t-phase and masks. The \(1/\sqrt{NI}\) cannot be dropped when interpreting the metaplectic residue. GaussianCrude.lean::gaussianFixedWindow_spectral_identity has a matching factor \((NI\,NJ^3)^2\) on its spectral-Summand-2 normalization; do not use the spectral expression without that factor.

If the UNWEIGHTED Dirichlet series \(D(w)=\sum_I\mathrm{columnWeight}(\Psi,I)(NI)^{-w}\) is proved to have a pole at \(w=5/6\), then the actual completed weight series \(D(w+1/2)\) has the corresponding pole at \(w=5/6-1/2=1/3\). Thus a dyadic NI~T main term scales like \(T^{1/3}\), NOT \(T^{5/6}\), before the outer physical and Mellin factors. This is an arithmetic normalization statement, not a claim that the actual twisted D has the posited pole.

## D. A precise cubic phase bridge ALREADY EXISTS at prime I

Detector/SourcePrime.lean::gaussTwo_prime_localGamma proves \(\mathrm{gaussTwo}((p))=\mathrm{localGamma}(p,2)\) for admissible primary prime p. The same module's corrected_prime_cubic_signal states
\[
\mathrm{localGamma}(p,2)\,\overline{\mathrm{angularFactor}(p)}
 \,\overline{G(p)}
 =-\mathrm{localGamma}(p,1)^{-1}.
\]
This is exactly the corrected prime cubic-Gauss factor, including angular and quadratic phases, not bare gaussTwo. Detector/SpectralCoefficient.lean::spectralSummand_source_coefficient retains additional targetMonoid(eta,I), reciprocitySign(I,s), the Xi cancellation, and the original completed mask. For squarefree composite I one must still prove the product/reciprocity and ray-character transfer from the original source. The corrected prime identity is the correct first bridge into metaplectic coefficients.

## E. What the original Patterson/metaplectic theorems do and do not supply

CubicMoment/Transform/MetaplecticHeight.lean defines the UNTWISTED Gaussian Dirichlet family
\[
\mathrm{metaplecticGaussSeries}(r,w)=\sum_u\mathrm{gauss}(ru)(Nu)^{-w}
\]
and its explicit \(5/6\) residue
\[
\mathrm{metaplecticResidue}(r)
 =A_0\,\mathrm{metaplecticTotient}(r)(Nr)^{-7/6}/
   \mathrm{metaplecticEulerAtTwo}(r).
\]
CubicMoment/Transform/MetaplecticMellinShift.lean::metaplectic_smooth_shift_of_polynomial provides the exact residue-plus-shifted-line integral; MetaplecticStripGrowth.lean::metaplectic_smooth_shift_of_published supplies published-input strip growth. CubicMoment/Estimates/TypeICompleted.lean::metaplectic_dyadic_height_of_published proves a uniform level/height mean
\[
 U^{1/2+\varepsilon}(Nr)^{1/4+2\varepsilon}\sqrt{T}
 + U^{5/6}(Nr)^{-1/6}/T^D
\]
for its specified metaplectic family.

Separately, CubicMoment/Theta/CubicThetaMains.lean::patterson_firstMoment and patterson_angularCancellation are PRIME first-moment/asymptotic results, with little-o for each FIXED nonzero angular mode. They do NOT directly furnish a meromorphic continuation for arbitrary detector ray twist \(\psi_{u_C}\), variable C and beta-masks, nor the asserted **uniform** \(O(U^{3/4+\varepsilon})\) remainder. Nor do the cited original modules establish the proposed \(\prod_{p|\beta}(1+(Np)^{-2/3})^{-1}\) depletion factor for the actual weighted source. Cubic-theta coefficients have reciprocity twists and are not freely deletable Euler-product coefficients.

**Elementary killer for automatic centering:** for a nontrivial character chi on finite group H, \(\sum_{u\in H}\chi(u)=0\), but \(\sum_u\chi(u)\chi(u)^{-1}=|H|\neq0\). A metaplectic phase can reverse the calibration character. Nonprincipal centering (#1011) alone therefore CANNOT prove a zero metaplectic residue. This algebra is certified abstractly in RH_Lean research/oai_434/VF919OriginalLowMetaProjection.lean (pending repository CI on the new commit).

## F. The EXACT missing theorem and acceptance route

1. Expand LowCompensation.lean::lowMarkedInverseRow_eq in the ORIGINAL pre-Cauchy physical source with COMPLETED J=1 and, first, K=0 selected slots. Retain S, sigma, eta, physical outer s, m, selected D and Mellin t; record the exact height/window and \(\sqrt{NI}\) factors.
2. Apply the ALREADY-PROVED SourcePrime.lean::corrected_prime_cubic_signal; extend from prime to all admitted squarefree I with CubicGaussCRT.lean and original SourceCoefficient/SpectralCoefficient reciprocity phases. This is the new source-to-metaplectic coefficient identification.
3. For each variable common C and exceptional k, split (k) into \(u_C\beta^6\), with support of \(u_C\) in G_C=jointFixedModulus*C. Track beta coprimality and the independently acting primal Mobius d projector.
4. Define \(\Lambda_{\rm actual}=\mathrm{Res}_{w=5/6}\,\mathcal D_{\rm actual,unweighted}(w)\) ONLY AFTER the source Hecke-series match is proved; the completed J=1 weight uses its shifted pole \(w=1/3\). Either show that the exact residue pairing across ray/calibration phases vanishes or extract its nonzero main term and pay it elsewhere. Do not posit unique ray class or unconditional vanishing.
5. Use the source-appropriate metaplectic strip/mean-square bounds with uniform C, beta and conductor costs to prove a genuine power saving on the FULL LOW-J PRE-CAUCHY PAIRED SOURCE. Combine with high-J CRT bound ONLY AFTER that bound has been certified in original-source Lean; then repay other high/multiplicity/sextic detector branches before any 7/8-delta assertion.

**Present genuine bottleneck:** actual source \(I\)-column (corrected prime-to-squarefree and ray/mask) -> untwisted/twisted metaplectic analytic family -> uniform residue projection. The existing Patterson prime asymptotic alone cannot decide \(\Lambda_{\rm actual}\).

Pinned references: Detector/{GramClassification,GramCanonicalSource,GramCanonicalBlock,GramSourceDivisors,GramFrequencyMass,GramIdealMass,GramJointFixed,SourcePrime,SpectralCoefficient,GaussianSeminorm,GaussianCrude,LowCompensation,LowCauchy,LowSeparated}.lean; Arithmetic/IdealMobius.lean; CubicMoment/{Transform/MetaplecticHeight,Transform/MetaplecticMellinShift,Transform/MetaplecticStripGrowth,Estimates/TypeICompleted,Theta/CubicThetaMains}.lean.
