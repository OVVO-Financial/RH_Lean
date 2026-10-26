# Compensated high-J CRT attack on the ORIGINAL OpenAI low detector (2026-10-25)

**Status: NEW SOURCE-FAITHFUL PAPER REDUCTION / EXACT EXPONENT AUDIT; NOT A LEAN-CERTIFIED GLOBAL ESTIMATE.** Pinned original source: openai/math@1581d4cbdd69a0faf34b2089614fe2a814316a6a. This continues draft PR #1022 without modifying its certified declarations. No new zero-free strip, Mertens exponent, canonical VF estimate, or RH is claimed.

## 1. The actual carrier and the lost phase

Original Detector/LowSeparated.lean defines the low integrand as a single signed pairing over m and ray sigma between lowRayAmplitude and the *original* correctedCompletedT. Detector/LowCauchy.lean::lowSeparatedIntegrand_cauchy takes the product of the separate low and inverse l2 energies. The ideal-column phase in correctedCompletedT then cannot reduce the low-only Gram: a signed inner product can be small while its first factor has large l2 norm. Any CRT improvement from the physical I,J source therefore has to be applied to the paired expression BEFORE this Cauchy step, or independently supply a genuinely stronger low-only Gram.

The physical inner character, at fixed outer s and completed ideals I,J, is the genuine factor
\[
  \rho_g(m)\;\mathrm{sexticGauss}(s,-m)\;
  \chi_I(m)\chi_J(m)^3,
\]
with all completedMask(S,D,I,J), completedCorrection, ray, Gaussian and mark factors retained outside the m-sum. The actual Cauchy theorem and original physical spectral reopening are separate existing facts, not an equivalence between low-only energy and the paired source.

On the original masked source I is squarefree and I,J are supported, but **the outer ideal s is not necessarily prime**. Detector/SpectralSupport.lean certifies squarefreeness of I; Detector/LowRayAmplitude.lean sums over all supported s.

## 2. New squareful-outer reduction to test (source adapter OPEN)

Let s be any nonzero supported ideal. By unique factorization in the Eisenstein PID, write
\[
 s=\prod_{\mathfrak p}\mathfrak p^{e_{\mathfrak p}},\quad
 s_0=\operatorname{rad}(s)=\prod_{\mathfrak p\mid s}\mathfrak p,\quad
 d_s=\prod_{\mathfrak p\mid s}\mathfrak p^{e_{\mathfrak p}-1},\quad
 N(s)=N(s_0)N(d_s).
\]

Original Detector/PhysicalCRT.lean::sexticGauss_coprime_product factors the outer Gauss sum over coprime prime powers, with m-independent reciprocity scalars. Original Detector/LocalPhysical.lean::sexticGauss_prime_power and Detector/PrimePower.lean::primePowerGauss_support imply that the whole outer Gauss factor vanishes unless \(d_s\mid (m)\). Write \(m=d_sn\) using compatible principal generators. Detector/PrimePower.lean::primePowerGauss_lift then reduces each prime-power Gauss factor to an \(N(\mathfrak p)^{e_{\mathfrak p}-1}\) multiple of a prime-modulus Gauss factor evaluated at a unit-scaled n. A local character raised to e divisible by six may become *principal*; its prime-modulus Gauss factor is then a Ramanujan mask, not an invented primitive character. It still depends periodically on n modulo that prime.

After restricting to surviving cells, the proposed reduced coefficient is periodic modulo a divisor of
\[
  g\,s_0\,\operatorname{rad}(IJ),
\]
where g is the original calibration generator. The completed-mask exclusions guarantee g is coprime to all good prime factors; the nonprincipal CRT calibration component then kills the complete zero frequency. This is consistent with, and NOT new relative to, original Detector/RadialIdentity.lean::actualCongruenceCoefficient_zero_frequency. The required new Lean adapter is the *full squareful support/lift and reduced-period identity with actual masks and unit factors*.

For the actual physical row, \(X_L=Z^{17/48}/L\) and the m-radial scale is \(Q_s=N(g)N(s)X_L\). The substitution \(m=d_sn\) changes it to
\[
  Q'_s=Q_s/N(d_s)=N(g)N(s_0)X_L.
\]
A safe candidate conductor is \(F=N(g)N(s_0)N(\operatorname{rad}(IJ))\), possibly larger than the minimal lcm conductor but still a valid period. Consequently
\[
  F/Q'_s \le N(\operatorname{rad}(IJ))/X_L \le N(I)N(J)/X_L.
\]
The factor \(N(d_s)\) from the Gauss lift must remain in the amplitude and be paid against the actual \(1/\sqrt{N(s)}\) row normalization; it must NOT be silently discarded.

For fixed smooth radial windows and fixed period, shifted 2D lattice Poisson has a zero-mean remainder \(O_{W,k}(M Q'_s(F/Q'_s)^{k/2})\) for any fixed k>2, where M majorizes the reduced coefficient (including Gauss lift). This does NOT independently bound the full outer/source/selected-slot sum.

## 3. Exact short-period corridor, and its limitation

Set \(\gamma=\log_Z L\), \(\sigma=\sum_{i\notin J_{\rm slot}}\ell_i\) (selected-slot exponent), \(t=\log_Z N(J)\), and take a fixed small Gaussian slack \(\eta>0\). The genuine slot geometry has \(0\le\gamma,\sigma\) and \(\gamma+\sigma\le1/6\). On a Gaussian bulk cell assume \(N(I)N(J)^3\le C Z^{1+\sigma+\eta}\). Constants from fixed windows are harmless for strict asymptotic exponents.

Then
\[
 \frac{F}{Q'_s}\ \ll\
 Z^{31/48+\gamma+\sigma+\eta-2t}.
\]
The Gaussian bulk also imposes \(3t\le1+\sigma+\eta+o(1)\) because \(N(I)\ge1\). Thus a strict short-period band
\[
  (31/48+\gamma+\sigma+\eta)/2<t<(1+\sigma+\eta)/3
\]
exists precisely when \(3\gamma+\sigma+\eta<1/16\). Its width is
\[
  \frac{1-48\gamma-16\sigma-16\eta}{96},
\]
and the maximum exponent margin from this argument is
\[
  1/48-\gamma-(\sigma+\eta)/3.
\]

This is a geometric reach calculation, not a proof that the whole low detector improves: at \((\gamma,\sigma)=(1/6,0)\), even the maximal Gaussian t fails the short-period condition. A claim that a short period uniformly covers every compensated tuple is FALSE.

## 4. Stronger primitive-CRT corridor survives ALL compensation splits (prime-s subsource)

For s a single good prime ideal of norm \(q\asymp Y_L=Z^{23/48}/L\), the genuine residual m-phase has local exponents
\[
 \begin{array}{c|c}
 \mathfrak p&\text{exponent mod 6}\\ \hline
 \mathfrak p=s&-1+\mathbf1_{s\mid I}+3v_s(J)\\
 \mathfrak p\mid I,\ \mathfrak p\ne s&1+3v_{\mathfrak p}(J).
 \end{array}
\]
Since I is squarefree, the second row is 1 or 4 modulo 6, always nonprincipal. If \(s\nmid I\), the first row is 5 or 2 modulo 6, even when \(s\mid J\); it is also nonprincipal. Hence the ORIGINAL prime-s and squarefree-I factors are a primitive local CRT family on sI, while the calibration g and any remaining J masks can be retained without deleting them. This is the fixed-source theorem TARGET from PR #1022, not a claim of a completed global analytic lift.

A finite Fourier/Gauss calculation with the primitive sI component and the remaining bounded mask yields the proposed uniform-in-radial-scale estimate
\[
 \frac{|S_{s,I,J}(Q_s)|}{Q_s}
 \ll_{W,g}
 \frac{N(\operatorname{rad}J)\sqrt{N(I)}}{X_L\sqrt{q}}
\]
(up to fixed calibration factors). Here \(S_{s,I,J}\) is the *normalized residual character sum after extracting the prime Gauss magnitude*, exactly as in PR #1022's primitive-column note. All outer completed-source coefficients remain to be summed.

Write \(d(J)=\log_Z(N(J)/N(\operatorname{rad}J))\ge0\). Substituting the Gaussian bulk upper bound and q,X_L gives the exponent
\[
 E=-\frac3{32}+\frac{\sigma+\eta}{2}
   +\frac{3\gamma}{2}-\frac t2-d(J).
\]
Thus the fixed-source ratio has a power saving whenever
\[
   t+2d(J)>3\gamma+\sigma+\eta-\frac3{16}.
\]

**Uniform high-J band, exact fractions:** fix \(\eta=1/384\) and
\[
 \frac{1+\sigma+\eta}{3}-\frac1{96}\le t
 \le\frac{1+\sigma+\eta}{3}.
\]
For every \(\gamma+\sigma\le1/6\), the exponent is
\[
 E\le -\frac1{96}+\frac\eta3+\frac1{192}
     =-\frac5{1152}.
\]
In fact the unused \(-7\sigma/6-d(J)\) margin makes many cells better. This provides a uniform *per-(s,I,J,L)* candidate saving \(Z^{-5/1152}\) on the high-J bulk face for all legal compensation splits, even those outside the short-period corridor.

**The dangerous s|I collision cannot occur in this high-J face.** Indeed if \(s\mid I\), then \(N(I)\ge q\asymp Z^{23/48-\gamma}\), so Gaussian support forces
\[
 t\le\frac{25/48+\gamma+\sigma+\eta}{3}+o(1).
\]
At the stated high-J lower edge the distance above this upper bound is
\[
 \frac{23/48-\gamma}{3}-\frac1{96}
 \ge \frac3{32}>0
\]
for every legal \(\gamma\le1/6\). This is a robust power-scale exclusion of prime-s/I collisions (constant norm-window factors do not alter the strict gap). Collisions s|J alone leave the s-local character nonprincipal, and must retain their true I/J masks.

**Scope:** a nonempty exponent face of the ORIGINAL compensated prime-s subsource has a uniform local CRT saving. The \(-5/1152\) is NOT a saving on the original compensated low operator \(Z^{3/16+254\epsilon}\), not a low-only Gram improvement, and not a beta below 7/8. The selected and unselected labels and the outer s,I,J source populations can consume the local saving. No global sum is bounded here.

## 5. Why compensation does not permit a naive assertion in either direction

Original Detector/LowSlotPolynomial.lean has \(\mathrm{lowUnselectedWeight}(a)\) containing \(L^{-3/2}\), while original Detector/LowNominalGeometry.lean gives \(X_L=X/L\) and \(Y_L=Y/L\). The primitive CRT fixed-source ratio above contains a compensating \(L^{3/2}\) factor. Thus the local \(L^{3/2}\) growth must NOT by itself be advertised as proof that the final low tuple necessarily loses power: the explicit outside \(L^{-3/2}\) is real. But neither may these L factors be canceled naively before inserting the actual \(\sqrt{Q}\) physical normalization, the s-sum, selected inverse row, fixed Gaussian profiles, and all source coefficients.

In particular, after the original Vstar completion the norm-only J prefactor is proportional to \(\sqrt{N(J)/T}\), NOT \(1/N(J)\). An argument that sums over J as a free harmonic series has lost the source completion and is invalid. The original compensated \(\ell^{6/5}\) and moment branches must be retained.

## 6. Reproducible exact exponent checks

All displayed identities are rational exponent arithmetic. Independent Fraction tests checked 20,000 rational parameter choices and the following exact edge fixtures:

| gamma | sigma | t lower | t upper | worst CRT E | s|I excluded? |
|---:|---:|---:|---:|---:|:---:|
| 0 | 0 | 373/1152 | 385/1152 | -293/1152 | yes |
| 1/6 | 0 | 373/1152 | 385/1152 | -5/1152 | yes |
| 1/12 | 1/12 | 45/128 | 139/384 | -13/128 | yes |
| 0 | 1/6 | 437/1152 | 449/1152 | -229/1152 | yes |

A minimal standard-Python Fraction reproduction is:

    from fractions import Fraction as F
    eta, lam = F(1,384), F(1,96)
    for gamma,sigma in [(F(0),F(0)),(F(1,6),F(0)),
                        (F(1,12),F(1,12)),(F(0),F(1,6))]:
        t = (1+sigma+eta)/3-lam
        E = -F(3,32)+(sigma+eta)/2+3*gamma/2-t/2
        collision_max = (F(25,48)+gamma+sigma+eta)/3
        assert E <= -F(5,1152)
        assert t > collision_max

The calculation certifies the exponent ledger only, not the analytic character estimate, actual ideal incidence, or completed-source summation.

## 7. Exact proof/attack gates, with owners and falsifiers

1. **Prime-s local character adapter** (first Lean target): reproduce the fixed-source CRT sI primitive factor including s|J phase, good-prime order-six hypothesis, calibration g, actual row masks, Fourier coefficient and all normalizations. Prove the displayed local estimate uniformly in Q. If a source-admitted good prime p|I acquires principal local exponent, show the smallest original counterexample (under s not dividing I).
2. **Squareful-s support/lift** (second Lean target): use sexticGauss_coprime_product, sexticGauss_prime_power, primePowerGauss_support and primePowerGauss_lift, with actual principal Ramanujan cases and zero/nonunit masks. Prove the exact reduced radial scale and periodic conductor. Do not import prime-only character claims for squareful s.
3. **Correct early signed pairing**: work from lowSeparatedIntegrand or original physical rows BEFORE lowSeparatedIntegrand_cauchy, expand original correctedCompletedT, preserve one occurrence of each (s,I,J) and all marked, Gaussian, calibration, ray and selected-slot labels. Isolate the high-J prime-s face and its complement at exact source level.
4. **Actual aggregate comparison**: pay the weighted s,I,J, unselected/selected, Gaussian-dyadic, principal/collision and exceptional sixth-power costs and prove a saving for the same complete operator appearing in Detector/LowCentralTuple.lean::low_central_compensated_tuple. Merely showing a pointwise \(Z^{-5/1152}\) ratio does NOT establish a power saving after summing. The first still-open quantitative inequality is precisely this full paired-source bound.
5. **Exceptional resonance falsifier**: the original sixth-power corridor contains coherent calibrated fifth-power seeds. Check those terms in the *same* aggregate before claiming nonprincipal averaging kills every low row. Existing PR #1022 note OAI_EXCEPTIONAL_SIXTH_CORRIDOR_SHARP_COUNT_SIGNED_GATE_20261025.md has the source-local counterexample.
6. Only AFTER a completed source-wide exponent is proved, reassess the high Gaussian, \(\ell^{6/5}\), incomplete sextic family, principal restoration and final \(7/8-\delta\) transfer. No proof here reaches this gate.

**Verdict:** exact new all-compensation high-J *local* power margin, exact exclusion of prime-s/I collisions there, plus a natural squareful-s prime-power lift to inspect. The missing mathematical advance is a source-authentic, uniform **aggregate signed pairing estimate**, not another algebraic restatement of the 7/8 boundary.

## Source paths (pinned)

- openai/math lean/OAI/NumberTheory/DirichletL/Detector/{LowSeparated,LowCauchy,LowSlotPolynomial,LowNominalGeometry,LowCentralTuple,PhysicalRows,PhysicalCRT,LocalPhysical,PrimePower,SpectralSupport,RadialIdentity,GaussianSeminorm}.lean
- RH_Lean PR #1022, research/{OAI_LOW_GAUSSIAN_CRT_PRIMITIVE_COLUMN_GAIN_20261025,OAI_LOW_GAUSSIAN_RESONANT_COLLISION_GLOBAL_A_GATE_20261025,OAI_EXCEPTIONAL_SIXTH_CORRIDOR_SHARP_COUNT_SIGNED_GATE_20261025}.md

No new Lean file, compiler result or original OAI theorem is asserted by this note. It is a reviewed-source mathematical attack candidate to be independently audited before formal promotion.
