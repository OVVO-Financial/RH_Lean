# Full-J quadratic CRT and squareful-s double-Fourier source attack
Date: 2026-10-25. Branch: PR #1022. Original source pin: openai/math@1581d4cbdd69a0faf34b2089614fe2a814316a6a.

**Scope / honesty:** This is a source-authentic, pen-and-paper LOCAL lemma and a CONDITIONAL complete high-J aggregate ledger. The local finite-field identities and rational exponents were independently tested for split and inert good-prime residue fields. It has NOT been imported as a warning-fatal Lean theorem on the actual OAI physical source, and it does NOT provide a global improvement from 7/8, since the complementary low-J region and other detector branches remain open.

## 0. Original source, exact support and normalization

Use ORIGINAL Detector/PhysicalRows.lean::physicalRowWeight and Detector/Row.lean::rowCoefficient, the true correction and marked mask from Detector/Completed.lean, squarefree I from Detector/SpectralSupport.lean, original Gaussian twisted window from Detector/GaussianSeminorm.lean, and original LowSlotPolynomial.lean for selected/unselected compensation. The fixed (s,I,J) physical m-dependent factor is

  f_{s,I,J}(m) = rho_g(m)*sexticGauss(s,-m)*idealRowHom(m,I)*idealRowHom(m,J)^3.

Here g = calibrationForSet(S).generator is the product of fixed excluded prime ideals, and the ORIGINAL masks imply g coprime to s,I,J. The set S contains fixed bad primes, so it is nonempty and the local calibration rho_g is nonprincipal at each factor of g. The I ideal is squarefree; J and s are arbitrary supported ideals.

For X_L=Z^(17/48)/L and Y_L=Z^(23/48)/L, the radial m-scale at s is

  Q_s = N(g)*N(s)*X_L.

The physical row weight before the m-sum has absolute size at most
  C_W / [Y_L * N(s) * sqrt(N(g)*X_L)]
times the raw sexticGauss(s,-m), where |tau|=1 for the original fixed calibration. The q=N(s) denominator combines sqrt(N(g)*q*X_L) with sqrt(q). Do not drop either.

The *specific* completed profile here is CompletedHeight.normTwistedSource gaussianFixedWindow t. Since
  gaussianFixedWindow(y)=gaussianAnnulus(y)/sqrt(y)
and
  Vstar(gaussianFixedWindow)(y)=gaussianAnnulus(y),
the norm of the original (I,J) completed summand on this profile is <= 2/N(J) (using |columnWeight(I)|/sqrt(N(I))<=1 and |cubeWeight(J)|<=1/N(J)). For other completed profiles this 1/N(J) weight cannot be asserted blindly.

## 1. Finite-field local lemma: double Fourier of a Gauss sum

Let k=O/p be a good prime residue field of cardinality q, chi=actualSextic(p) of exact order six, and psi a nontrivial additive character. Extend all multiplicative characters by zero at 0, INCLUDING the principal multiplicative character. For a>=1 write

  G_a(n)=sum_{x in k} chi(x)^a psi(nx).

With Fourier transform hat f(xi)=sum_{n in k} f(n)*psi(-xi*n), additive orthogonality yields the EXACT formula

  hat G_a(xi)=q*chi(xi)^a.

This identity applies for 6|a too: then chi^a is principal with zero at the origin, and G_a is a Ramanujan factor, NOT a primitive sextic character. In either case
  max_xi |hat G_a(xi)|<=q and hat G_a(0)=0.

The source multiplies G_a(n) by the local characters of I and J. For a=1 and alpha=v_p(I) in {0,1}, beta=v_p(J)>=0, the local product is (for units n) Gauss(chi) * chi(n)^(alpha+3*beta-1).

- alpha=0: exponent -1+3*beta is 5 (beta even) or 2 (beta odd) modulo 6, always nonprincipal. Fourier magnitude <=q.
- alpha=1, beta odd: exponent 3 modulo 6, nonprincipal quadratic. Fourier magnitude <=q.
- alpha=1, beta even: exponent 0 modulo 6, principal coprimality mask; Fourier magnitude <=q^(3/2). This is the real s|I collision, and the extra sqrt(q) is charged to sqrt(N(I)).
- If a>=2 and alpha+beta>0, writing m=d_s*n forces p|m, so the ORIGINAL I/J characters vanish identically. The term is ZERO; it must not be treated as an independent primitive character.
- If a>=2 and alpha=beta=0, the local factor is G_a(n), with Fourier max q by exact double Fourier, including 6|a.

All cases satisfy the local bound
  sup_xi |Fourier(local source)|<=q^(1+alpha/2+beta/2).

For p not dividing s:
- alpha=1: exponent 1+3beta is always nonprincipal; Fourier norm sqrt(q) <= q^((alpha+beta)/2).
- alpha=0, beta odd: quadratic, Fourier norm sqrt(q) <= q^(beta/2).
- alpha=0, beta even >=2: principal mask, Fourier norm <=q <=q^(beta/2).
- alpha=beta=0: omit p from the conductor.

At excluded p|g the original rho_g is a nonprincipal local character (norm of Fourier transform <=q suffices), and since p is not in sIJ this guarantees the FULL global Fourier zero mode vanishes even on s|I principal-collision cells. This is consistent with the pre-existing Detector/RadialIdentity.lean::actualCongruenceCoefficient_zero_frequency; zero-mode vanishing is NOT a new OAI theorem.

## 2. Composite-s exact support and normalized local theorem TARGET

Factor s=prod_p p^a, s0=rad(s), d_s=s/s0. Original Detector/PhysicalCRT.lean::sexticGauss_coprime_product, Detector/LocalPhysical.lean::sexticGauss_prime_power, and Detector/PrimePower.lean::primePowerGauss_support + primePowerGauss_lift give

  sexticGauss(s,-m)=0 unless d_s|m.

Choose compatible primary generators and write m=d_s*n. The original Gauss factor then equals

  N(d_s)* phase(s) * prod_{p^a||s} G_{chi_p^a}(u_p*n),

with |phase(s)|=1 and u_p a residue unit determined by CRT choices. This expression contains the ACTUAL imprimitive/principal a divisible by 6 factors. The other source characters at d_s*n are either zero (if gcd(d_s,IJ)>1) or an m-independent unit phase times their original characters of n. Since g is excluded, gcd(d_s,g)=1.

The surviving coefficient in n is periodic on the SQUAREFREE ideal
  f = g * lcm(s0, rad(IJ))
(not the redundant product g*s0*rad(IJ) in collision cells). CRT prime-by-prime and section 1 imply

  |hat f_source(xi)| <= C_g*N(s0)*sqrt(N(I)*N(J))
for EVERY frequency xi. Its frequency-zero coefficient is 0 due to rho_g.

**Uniform fixed-source proposition, to certify in actual original Lean:**
For every fixed smooth compact supported W0 in (0,infty), all supported outer s, squarefree admitted I, admitted J, g coprime sIJ,
and all Q_s=N(g)N(s)X_L with X_L>0,

  |sum_{m in O} f_{s,I,J}(m) W0(N(m)/Q_s)|
      <= C_{W0,g}*N(s)*sqrt(N(I)*N(J)).

Proof: m=d_s*n reduces the radial scale to Q'_s=N(g)N(s0)X_L, and multiplies the local product by N(d_s). On the shifted Eisenstein lattice for conductor f, Poisson plus zero-mean cancellation gives
  |sum_n f_source(n) W0(N(n)/Q'_s)|
    <= C_W sup_xi |hat f_source(xi)|.
Uniformity in all Q'_s follows from
  sum_{k !=0} |hat V(r*k)| <= C_V*r^(-2)
for radial V(x)=W0(||x||^2), r>0. The lattice O is fixed and multiplication by a generator of f is a rotation/dilation. Multiply by N(d_s) and N(s0)=N(s)/N(d_s). The resulting bound is uniform in the prime-power exponents of s.

**Important:** This uses the second Fourier transform of the ACTUAL Gauss factor. Replacing that Gauss factor by a principal CHARACTER before transforming creates a fictitious norm penalty at a≡0 mod6. The genuine collision a=1 and p|I can create a q^(3/2) local coefficient, but sqrt(N(I)) explicitly pays it.

The final statement is source-level pen-and-paper arithmetic/Poisson. It is not yet a repository-level compiled theorem; produce explicit original Lean bridge lemmas before claiming certification.

## 3. Complete high-J slice: conditional absolute source budget

With the preceding uniform local proposition, insert the actual physical prefactor. For fixed s,

  |physical (s,I,J) m-pairing|
    <= C_{W0,g}*[sqrt(N(I)*N(J))]/[Y_L*sqrt(X_L)].

The N(s) from the double Fourier/Lift cancels the 1/N(s) from original physical normalization. No separate outer squarefull Rankin bill is needed here. The number of supported ideals s with a Y_L<=N(s)<=b Y_L is O_{a,b}(Y_L), by ordinary ideal/lattice counting in O=Z[omega]. Summing over s yields the same bound with 1/sqrt(X_L).

The true completed gaussianFixedWindow coefficient is <=2/N(J), hence the source at fixed selected b and unselected a is majorized by

  C * L^(-3/2) / sqrt(X_L) *
    sum_{admissible I,J, D|I*J^3} sqrt(N(I))/sqrt(N(J))
  = C * Z^(-17/96) L^(-1) *
    sum_{admissible I,J,D|I*J^3} sqrt(N(I))/sqrt(N(J)),

where D=m_sel is squarefree. In particular D|I*J^3 iff D|IJ (true ideal divisibility). Write D=D_I D_J on coprime allocations. There are <=2^K allocations, and standard ideal divisor counting on one dyadic J range V<=N(J)<2V, with N(I)<=U, gives

  sum_{D|IJ, NI<=U, V<=NJ<2V} sqrt(NI)/sqrt(NJ)
    <= C_K * U^(3/2)*V^(1/2)/N(D).

After summing unselected prime-slot labels,
  sum_a 1/L <= polylog(Z) (K fixed).
After summing selected b labels,
  sum_b 1/N(D) <= polylog(Z) (K fixed).
No signed source cancellation is presumed in either sum. All fixed W0,W1, t-profile phases have bounded norms; a uniform original Gaussian-tail and Mellin integration still need separate certification.

On a top-J band t=log_Z(N(J)) with
  t >= (1+sigma+eta)/3-lambda,
the original completed Gaussian support N(I)*N(J)^3 <= C Z^(1+sigma+eta) gives
  U <= C Z^(1+sigma+eta-3t) <= C Z^(3lambda).
**No +3gamma occurs here:** the completed inverse height T=Z^(1+sigma+shift) is NOT the physical m-scale X_L or Y_L.

Then the complete (all supported s, all marked I,J, all selected/unselected labels) high-J slice obeys the conditional paper bound

  |A_topJ| <= C_epsilon * Z^(-17/96 + 3*(1+sigma+eta)/2 -4*t_min + epsilon)
          = C_epsilon * Z^(-1/96+(sigma+eta)/6+4lambda+epsilon).

Example eta=lambda=1/384 and sigma<=1/6: the upper exponent is 65/2304, whereas the original low-Cauchy benchmark 3/16=432/2304. The numerical gap is 367/2304. At sigma+eta=1/8, eta,lambda -> 0, the exponent tends to 1/96 (versus 18/96).

Crucial scope: (1) local composite-s analytic estimate, (2) the replacement of the original low pre-Cauchy source by this full ideal/tuple sum, (3) the Gaussian tail and dyadic t integral are still to be formalized. This is not a bound for LOW_CENTRAL_TUPLE globally; LOW-J and the high Gaussian/multiplicity/moment detector branches remain open.

## 4. Mechanism B as an independent backup

For squarefree selected D, let D_I=gcd(D,I), D_J=D/D_I. Since D|IJ, D_J|J and coprime I. At primes p|D_J with odd v_p(J), quadratic Gauss gives p^(-1/2) versus the old crude modulus. With even v>=2, the old radical deficiency N(rad J)/N(J) itself gives at least p^(-1). Thus the improvement over the previous relaxed source bound is at least N(D_J)^(-1/2).

The TOP-J Gaussian bound gives N(D_I)<=N(I)<=Z^(3lambda+o(1)), so N(D_J)^(-1/2) <=Z^(-sigma/2+3lambda/2+o(1)). Applying this once, not double-counting the same J prime in another improved coefficient, changes the previous aggregate exponent to

  5/32 - sigma/6 + eta/3 + 5lambda + epsilon.

At sigma=1/8 and eta,lambda -> 0 this is 13/96 (<3/16=18/96). Mechanism A (full J) is stronger, and the marked-prime method is a useful diagnostic if complete J quadratic CRT cannot be formalized.

## 5. Correction: the proposed 100% outer Rankin deficiency tail is false

A tempting tail is
  sum_{N(s)/N(s_prim) >=Z^d0} 1/N(s) << Z^(-d0+epsilon),
where s_prim retains primes of exponent a NOT divisible by six. This is FALSE for general supported s, because s=p^6 has s_prim=1 and N(s)/N(s_prim)=N(p)^6. For p in [U,2U], d0 defined by U^6~Z^d0, the harmonic sum over such sixth powers has order U^(-5)/log U (by the prime ideal theorem on split good prime ideals), not U^(-6+small exponent). The correct uniform Rankin exponent for this particular deficiency is at most 5/6 (up to epsilon). A 5/6 tail still beats a 1/2 local penalty, but using it is unnecessary for the double-Fourier fixed-source proposition above.

Also: a=6 local chi^a is PRINCIPAL, not a primitive quadratic/sextic character. Its genuine Gauss factor is a Ramanujan sum, whose SECOND Fourier transform remains exactly q*chi^a. Do not divide a principal Gauss norm by sqrt(q) by fiat.

## 6. Original modules and formal proof order

1. CubicSieve/Poisson.lean::norm_canonicalGaussSum_of_nontrivial, canonical_polya_vinogradov_of_nontrivial; Detector/Sextic.lean::actualSextic_pow_eq_one_iff; Detector/PrimePower.lean::primePowerGauss_lift/support; Detector/PhysicalCRT.lean::sexticGauss_coprime_product.
2. Formalize the finite-field double-Fourier lemma for prime Gauss as a function of the FREQUENCY n; both principal and nonprincipal cases. Formalize the six local I/J collision cases with the original zero/nonunit mask. Then CRT tensorize on exact squarefree lcm conductor f.
3. Prove the support/lift m=d_s*n and \(\hat f_{\rm source}(0)=0\) under the ORIGINAL completed/calibration masks, with W0 rescaled.
4. Derive uniform original radial Poisson \(\ll Ns\sqrt{NI NJ}\), then sum actual s with PhysicalRows.lean normalization.
5. Derive the squarefree marked incidence \(\ll U^{3/2}V^{1/2}/ND\); sum actual selected/unselected tuples. The easy rational exponent equality is in a separate proposed 4.34.1 arithmetic-budget Lean module.
6. Handle the Gaussian tails, real t integration, non-top J range, and *other original detector branches*. Do not infer global 7/8-delta until those are paid.

## 7. Finite falsifier

A standard-library finite-field source-local Gauss/Fourier probe checks q=7,13,19 (split-degree-1) and q=25,121 (inert-degree-2 Eisenstein cases) across outer exponents a=1..12, I incidence alpha=0,1, and J valuations beta=0..5. It verifies the double transform and the q^(1+alpha/2+beta/2) local bound, including sixth-power Ramanujan and s|I collisions. This tests local arithmetic only; it does NOT evaluate the fully labeled original OAI low source or certify an analytic theorem in Lean.

## 8. Wider high-J corridor (exact unconditional rational arithmetic)

The bound is not limited to a narrow face with lambda=1/384. For each dyadic J-cell at t=log_Z N(J), the CONDITIONAL absolute bound before choosing t_min is
\[
 E(t)=-17/96+\tfrac32(1+\sigma+\eta)-4t.
\]
It beats the existing full low-Cauchy exponent 3/16 whenever
\[
 t>\frac38(1+\sigma+\eta)-\frac{35}{384}.
\]
The top support edge is \(t_{\max}=(1+\sigma+\eta)/3\), so its strict width is
\[
 t_{\max}-t_{\mathrm{crit}}=\frac{35}{384}-\frac{1+\sigma+\eta}{24}.
\]
If \(\sigma+\eta\le1/6\), this is \(\ge49/1152>0\). The relative saving must shrink by the chosen distance from \(t_{\mathrm{crit}}\), any source tail constants and epsilon; the endpoint itself has zero margin. The rational identities have corresponding Lean-only-budget lemmas in VF919OriginalLowQuadraticBudget.lean. This is again ONLY the high-J source, not the full original low theorem.

