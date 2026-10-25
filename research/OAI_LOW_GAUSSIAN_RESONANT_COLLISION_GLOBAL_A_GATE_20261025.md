# Actual low Gaussian: collision split and Global Theorem A audit
2026-10-25. Source pinned: openai/math@1581d4cbdd69a0faf34b2089614fe2a814316a6a.
This is an audited source-local mathematical attack, NOT a compiled global detector estimate, a new Mertens exponent, or RH.

## Actual original source and collision

Detector/PhysicalReopen.lean gives the m-dependent character at fixed supported (s,I,J):
  C.residueMonoid(m) * sexticGauss(s,-m) * idealRowHom(m,I) * idealRowHom(m,J)^3.
Detector/Completed.lean::completedMask requires the original I*J^3 to avoid all excluded primes. Detector/LowRowMellin.lean requires s to avoid the same excluded primes. Calibration.lean::calibrationForSet is a CRT product of nonprincipal local calibrations; the actual application assumes fixedBadPrimes is contained in the excluded set S, so S is nonempty and contains the norm-3 lambda prime and the norm-4 ideal (2).

At each prime of the squarefree I column, the local exponent is 1+3*v_p(J), congruent to 1 or 4 mod 6: NEVER principal. If the low prime s divides I, unique ideal factorization and squarefreeness give
  I = s * I',  IsRelPrime(s,I'),  Squarefree(I'),
  N(I) = N(s)*N(I').
The local s exponent in that case is (-1)+1+3*v_s(J), congruent to 3*v_s(J) mod 6.

Under UNCOMPENSATED bulk bounds q=N(s)>=Z^(23/48) and N(I)*N(J)^3<=Z^(1+1/384), N(J)<=Z^(385/1152)<q for Z>1, hence s does not divide J. The s character in the collision is then a PRINCIPAL COPRIMALITY MASK, not a primitive Gauss factor. The putative v_s(J) odd quadratic subcase does not occur in this unscaled Gaussian region. The proof must re-check this for compensated physical scales, where q can be smaller.

## Important existing certified theorem: calibrated zero mode is already absent

Original Detector/RadialIdentity.lean::actualCongruenceCoefficient_zero_frequency proves, for EVERY A and s with nonzero generators, an admissible coprime calibration g, and ANY nonempty excluded-prime set S:

  actualCongruenceCoefficient (calibrationForSet S hS) A s hA 0 = 0.

This is source-authentic and PRE-EXISTING in pinned OpenAI. It includes the coherent s|I and J-square towers. It follows from the calibrated source vanishing at frequencies not coprime to g; H=0 is always excluded when S is nonempty. Therefore the fact that our primitive-factor CRT vanishes at zero, BY ITSELF, is not a new route around 7/8. The genuinely additional possible improvement is a better UNIFORM upper bound on its NONZERO frequencies and especially the physical weighted/Gram energy after compensation.

The new s*I primitive CRT route may still improve nonzero-frequency coefficients, but it MUST be compared numerically and analytically to the existing original FFT/Mellin frequency estimates. Do not count already-certified calibration zero-frequency vanishing as a new power saving.

## Correct calibrated primitive CRT factor, both cases

Assume the source's original masks, and g coprime s*I*J. Write G for primitive local-character primes and H for remaining masks/imprimitive factors.

NONCOLLIDING s does not divide I:
  G = (g)*s*I,
  H = product of prime ideals p|J not dividing I.
The factor on s is inverse sextic (exponent 5); the factor at p|I has exponent 1+3*v_p(J) in {1,4} mod 6; the factors of g are nonprincipal localCalibration characters. Thus G is primitive at every constituent prime.

COLLIDING I=s*I', with s not dividing J:
  G = (g)*I',
  H = s * product of prime ideals p|J not dividing I'.
The s-component is principal on units and zero on nonunits; retain it in H. In particular, if I'=1 and J=K^2, the original nonprincipal calibration component (g) is ESSENTIAL to exclude a zero Fourier mode. Without calibration, the pure s-principal mask has nonzero complete mean.

For finite additive Fourier transforms, original Detector/PhysicalCRT.lean gives the CRT factorization. The true primitive local Gauss norm is sqrt(N(p)), and the remaining H Fourier transform is bounded trivially by N(H). Hence:
  |hat chi(k)| <= N(H)*sqrt(N(G)),   hat chi(0)=0.
The latter holds because the original calibration conductor g is nonempty and carries a nonprincipal local character.

After the 2D Eisenstein radial Poisson transform for a fixed compact smooth W, for EVERY Q>0,
  |sum_m chi(m)*W(N(m)/Q)| <<_W N(H)*sqrt(N(G)).
The s-collision case has lost a primitive sqrt(q), but gained a principal H factor q. Accounting for I=s I' restores exactly the same source-local relative estimate as the noncollision case:
  |S_{s,I,J}(Q_s)|/Q_s
    <<_W N(rad J)*sqrt(N(I))/(X*sqrt(N(g)*N(s))),
  Q_s=N(g)*N(s)*X.

At the UNCOMPENSATED X=Z^(17/48), N(s)~Z^(23/48), NI*NJ^3<=Z^(1+1/384), t=log_Z NJ, d=log_Z(NJ/N(rad J)), this yields
  |S|/Q_s <<_W Z^(-71/768-t/2-d)/sqrt(N(g)).
This is a fixed-source theorem target, not yet a compiled Lean detector estimate. The s|I substitution is NOT a free additional Z^(-23/48) saving; all factors and outside weights must be counted.

## Exact compensated L cost (critical Global Theorem A obstruction)

The REAL low compensated source uses
  X' = Z^(17/48)/L,  Y' = Z^(23/48)/L,
where L is the norm of an unselected-slot product. See Detector/LowOriginalPools.lean, Detector/LowNominalGeometry.lean and Detector/GaussianSubset.lean.
With q~Y', the geometry of the same bound includes
  1/(X'*sqrt(q)) ~ L^(3/2) * Z^(-17/48-23/96).
Even temporarily retaining the unscaled NI*NJ^3 cutoff, the relative local estimate becomes
  |S|/Q_s << Z^(-71/768-t/2-d)*L^(3/2)/sqrt(N(g)).
Since original selected-slot widths permit total exponent up to 1/6, the potential L^(3/2) cost is Z^(1/4), greater than the minimum Z^(-71/768) gain. Gaussian source scales also change in compensated modes. The genuine compensation coefficients and mask/slot exclusions MUST independently pay this cost. No unconditional uniform all-compensations gain is currently established.

## Energy vs signed source: no automatic squaring

A fixed-source Fourier pairing bound is NOT a power saving on
  G_low = sum_u omega_u*|F_u^low|^2.
For example any nonprincipal finite character chi has sum_x chi(x)=0 but sum_x |chi(x)|^2=#units. Thus a signed zero mode can vanish exactly while a positive diagonal energy remains unchanged.

To prove global Theorem A with a factor Z^(-71/384), one must establish a source-authentic L-uniform Gram/energy transfer over the actual s,I,J, ray, selected slots, Gaussian dyadics, and compensation labels. Also certify the m-independent source coefficients and Gaussian tails. A harmonic J sum alone gives only logarithmic control; the original I weight is columnWeight(I)/sqrt(N(I)) multiplied by Vstar, which itself contains sqrt(N(I)*N(J)^3/Z). It is not a free 1/N(I) harmonic suppression.

## Exact original completion weight: harmonic cubeWeight DOES NOT survive Vstar

Read Original Arithmetic/IdealMobius.lean:
  cubeWeight(Psi,J) = angular_J*Psi(J)^3/N(J)
  Vstar(W,y) = sqrt(y)*W(y),
  summand(Psi,W,Z,I,J)
    = columnWeight(Psi,I)/sqrt(N(I)) * cubeWeight(Psi,J)
      * Vstar(W,N(I)*N(J)^3/Z).

For positive norms a=N(I), b=N(J), straightforward exact cancellation gives
  [1/sqrt(a)] * [1/b] * sqrt(a*b^3/Z) = sqrt(b/Z).
Thus after completing the ORIGINAL source, the norm-only prefactor is
  columnWeight(Psi,I)*angular_J*Psi(J)^3*sqrt(N(J)/Z)
  times W(N(I)*N(J)^3/Z),
NOT columnWeight(I)/sqrt(NI)*[1/NJ] with a harmonic J sum.

Consequences:
- There is NO isolated 1/sqrt(NI) outside the completed Gaussian window that can be booked as a free suppression on I=sI'.
- There is NO general O(log Z) upper bound on the full completed J-source by summing 1/N(J): the Vstar factor changes the absolute J norm power to +1/2. The combined I/J Gaussian support may still make the TOTAL source summable, but that is a different weighted calculation and must be proved with original coefficients.
- The principal collision I=sI' can have a smaller I-fiber cardinality, but its savings must be measured against this correctly normalized completed source and the s-sum.

This explicitly invalidates the proposed immediate Step 2 summation based solely on cubeWeight harmonicity.

## Exact existing full compensated low acceptance baseline: 3/16

Original Detector/LowCentralTuple.lean::low_central_compensated_tuple already establishes the actual sum over all labeled unselected slots and selected subsets, with the original physical row, Gaussian completion and compensation factors:
  norm(complete compensated low-central tuple)
    <= C*(1+norm(t))^degree * Z^(3/16+254*epsilon)
under its stated hypotheses, INCLUDING selected slot exponents totaling at most 1/6.

The proof tracks the real L payment in low_central_compensated_tuple and low_compensated_sqrt_factor, together with the original lowGramFactor and inverse-family bounds. A genuine beta=7/8-delta improvement by the proposed low route requires a NEW estimate for this SAME fully compensated operator, with exponent 3/16-delta (up to stated controllable epsilon loss), or an explicitly matched replacement global detector contract.

A direct alternative is a signed bilinear theorem on the full low *paired* source (after spectral reopening) with uniform absolute coefficient/slot budget. The local CRT bound pairs with the inverse row; it cannot be squared into a bound on G_low by ignoring its positive diagonals. The relevant exact necessary ledger is:
  |signed_low(Z)| <= sum_{labels} |outside_weight(labels)|*|physical_m_pairing(labels)|.
The new input supplies only physical_m_pairing <= Q_s*Z^(-71/768-t/2-d)*L^(3/2)/sqrt(N(g)) in the applicable bulk. The other weighted coefficient/slot sum must be proved independently, keeping all Gaussian tails and noncoprime cells.

In particular do NOT advertise Global Theorem A as immediate from a harmonic J sum; the existing original full source has already spent a distinct 3/16 exponent at the Gram/compensation level. We must prove an improvement relative to THAT bound.

## Exact next acceptance test

(1) Warning-fatal Lean: s|I implies I=s I', coprime squarefree I', and exact norm; with NI/NJ bounds isolate s not dividing J and principal s character.
(2) Warning-fatal Lean: extend the original finite CRT Gauss theorem to the actual CALIBRATION local characters and the correct primitive G and mask H in both cases.
(3) Warning-fatal Lean: original weighted Poisson row with a uniform fixed-W Fourier tail and original Q_s.
(4) Independent original-source inequality: transfer local signed saving into the FULL positive low Gram while paying L^(3/2), source counts and nonprincipal/principal terms.
(5) Only after all (1)-(4) establish any global energy power bound, and only after the other high, multiplicity and moment branches are reoptimized, claim beta<7/8.
