# Original OAI low-Gaussian: exact unit projection and radical-conductor Poisson attack
2026-10-25. Source pin: openai/math@1581d4cbdd69a0faf34b2089614fe2a814316a6a.
Source math is unconditional for the **specified original fixed (s,I,J) subsource**; neither the global 7/8 detector nor RH is improved here.

## A. Literal source factor, with masks preserved

The original files Detector/PhysicalRows.lean, Detector/Completed.lean,
Detector/Row.lean, Arithmetic/IdealMobius.lean show that after expanding
one actual correctedCompletedT pair of ideals (I,J), the m-dependence in
the original s-th outer low-Gaussian summand is precisely

  T_s,I,J(m) =
      C.residueMonoid(m)
      * sexticGauss(s,-m)
      * idealRowHom(m,I)
      * idealRowHom(m,J)^3.

The row's other original factors are m-independent: excluded/marked
completedMask(S,D,I,J), completedCorrection(I,J), GaussTwo(I),
fixed η/Xi and reciprocity phases, the W1 and ray coefficients,
1/(sqrt(N(I))*N(J)), and gaussianCompletedProfile(N(I)*N(J)^3/Z).
The m-dependent physical W0 window is W0(N(m)/Q_s),
where Q_s = N(C.generator)*N(s)*X.

For **prime supported s**, original
Detector/CalibrationRemoval.lean::sexticGauss_unit_scale shows
sexticGauss(s,-m) has inverse χ_s(m) character dependence on units
and vanishes when s divides m. Thus, up to an m-INDEPENDENT constant,

  T_s,I,J(m) =
      rho_C(m)*conj(chi_s(m))*chi_I(m)*chi_J(m)^3

with the original zero/nonunit masks. This is a genuine finite
multiplicative character on O/f with a conductor f dividing

  (C.generator)*s*rad(I*J).

The radical improvement is certified in original
Detector/RowRadicalConductor.lean::idealRowHom_congr_radical.
It is ESSENTIAL: original Detector/PhysicalPoisson.lean uses the
oversized period (C.generator)*s*A with A=I*J^3. Replacing A by its
radical for the actual m dependence is what opens the new conductor
range; the original oversized period does NOT show the saving.

For C=calibrationForSet(S), the original actual coefficient is
connected to the bare one via original
Detector/CalibrationRemoval.lean::actualCongruenceCoefficient_calibration_factor,
when the completed mask and original s-admission make the entire
A*s coprime to the calibration generator.

## B. ZERO-FREQUENCY theorem in exact original OAI source

The already-certified source theorem
Detector/LocalUnitFrequency.lean::bareCongruenceCoefficient_unit_frequency
asserts, for b coprime to A*s,

  B_A,s(b*H) = lambda_A,s(b) * B_A,s(H),
  lambda_A,s(b) = idealRowHom(b,A)^(-1)*idealRowHom(b,s).

Setting H=0 gives B_A,s(0)=lambda_A,s(b)*B_A,s(0).
Thus whenever lambda_A,s(b) is nontrivial, B_A,s(0)=0.
This is exact, not a statistical heuristic or an average.

New research/oai_434/VF919OriginalLowNonresonantZeroMode.lean
proves this original bare zero-mode corollary, then carries the
vanishing through the REAL calibrated coefficient via the above
original OAI calibration-factor identity. Warning-fatal CI is needed
before calling those two corollaries Lean-certified.

An even cheaper exact exclusion works at the lattice level: if
the residual multiplicative character is nontrivial on any Eisenstein
unit u in {+/-1,+/-omega,+/-omega^2}, radial W0 and the full O-lattice
imply the sum is exactly zero by reindexing m -> u*m.

## C. UNCONDITIONAL source-local power saving via short radical conductor

For the physical scales X=Z^(17/48), Y=Z^(23/48), assume:
- s is a good prime supported numerator ideal with N(s) comparable to Y,
  and coprime to the genuine excluded calibration conductor;
- I is a squarefree good column ideal, and the true completed-mask
  and original ray correction do not kill the (I,J) pair;
- N(I)*N(J)^3 <= Z^(1+1/384);
- Z^(21/64) <= N(J) <= Z^(1/3).

Then automatically

  N(I) <= Z^(7/384)  < N(s)  ~ Z^(23/48),
  N(J) <= Z^(1/3)   < N(s).

Hence s divides neither I nor J: χ_s cannot be canceled by their
sextic/cubic factors nor by rho_C (whose conductor avoids s).
The residual character is NONPRINCIPAL on O/f and has exact
complete-conductor mean zero.

With F=N(f), Q_s=N(C.generator)*N(s)*X,

  F/Q_s <= N(I)*N(J)/X
        <= Z^(1+1/384 -17/48 -2*(21/64))
         = Z^(-1/128).

The interval is genuinely nonempty:
1/3-21/64=1/192>0.

Elementary shifted-lattice Poisson summation for any *fixed*
C-infinity compact radial W0 yields (for Fourier order k>2)

  |sum_(m in O) chi(m) W0(N(m)/Q_s)|
      <= C_(W0,k) Q_s (F/Q_s)^(k/2)
      <= C_(W0,k) Q_s Z^(-k/256).

Here **the zero Fourier mode is removed by actual source arithmetic**,
and every nonzero mode is rapidly decaying. For k=4 this is an
unconditional factor Z^(-1/64) in the selected ORIGINAL m-sum.
The raw unnormalized sexticGauss contributes an additional sqrt(N(s))
prefactor; the original lowPhysical weight contains 1/sqrt(N(s)).
All other outside amplitudes, source counts and principal terms
must still be paid before a detector power bound is possible.

Proof of uniformity: as O=Z[omega] is a PID, f=(d), with N(d)=F.
Split the lattice into F cosets r+dO. For the Schwartz function
V(z)=W0(N(z)), the sum on each coset is (Q_s/F)*cV plus an
O_(W0,k)((Q_s/F)^(1-k/2)) shifted Poisson error, uniform in r
because multiplication by d is a rotation/dilation of O.
The constant main term disappears when summing the nonprincipal
chi(r) over its F residue classes. Multiplying the uniform error
by F gives the bound above. This is classical shifted-lattice
Poisson and does not require an NNS stochastic independence axiom.

A C-infinity Gaussian in log(N(I)N(J)^3/Z) suppresses the far
outside-Gaussian region superpolynomially, but a FULL uniform
aggregate bound over its tails has NOT been proved in this PR.

## D. Numerical source tests (not a full detector evaluation)

The full local source-factor script scanned 96 cases at Q values
4,096 to 524,288, with and without an illustrative norm-2/3 mask.
The physically matched cubic script scanned 11 J primes with
Z=N(J)^3, X=Z^(17/48), Y=Z^(23/48), s near Y, Q_s=N(s)X:
- 9 of 11 unit-nontrivial cases have zero radial signed sum to
  floating-point noise (<=5.1e-17 relative);
- the other two unit-trivial cases show real, nonzero ratios:
    (J,s)=(13,37): 0.078191395
    (J,s)=(37,181): 0.0105605865
  at physically matched Q_s. This precisely matches computing
  residual unit exponents at -1 and omega.
- coherent tower I=s, J=P^2 remains exactly coherent;
- genuine complete CRT nonprincipal characters have ZERO exact
  complete-residue sum, whether or not unit symmetry alone kills them.

Only the m-dependent factor was evaluated numerically. This is
an actual original subsource, not an evaluation of all calibration,
fixed correction, W1, Hecke, Gaussian/J/I totals, Mellin or the
full heavy-slot powerset. Unit-projected zero is algebraic,
but the reported nonzero coherence ratios are finite observations.

## E. The next genuinely unsolved arithmetic and analytic bills

1. Certificate of actual calibrated zero-frequency vanishing (new Lean).
2. Construct and certify the shorter (g)*s*rad(A) Poisson conductor
   in the ORIGINAL physical source, not only its existing g*s*A
   period. Reuse idealRowHom_congr_radical; retain actual masks.
3. Prove the k=4 or higher shifted-period Poisson inequality in
   the original weighted source with constants UNIFORM in variable
   calibration g, s, I, J and fixed source windows.
4. Sum the high-J nonprincipal sector over *all* s,I,J and the
   compensating subsets, keeping original source normalization.
5. Pay the low-J range N(J)<Z^(21/64), the surviving unit-trivial
   and resonant towers, principal/collision charges, and complete
   Gaussian tails. A saving in the high-J sector alone is NOT
   an improvement in the 7/8 global Mertens exponent.

The important result is a source-authentic, unconditional *local*
cancellation and an explicit nonempty asymptotic scale band.
No statement here concludes M(x)=O(x^(7/8-delta)) for delta>0.
