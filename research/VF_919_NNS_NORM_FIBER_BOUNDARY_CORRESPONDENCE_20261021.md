# Genuine ideal-label norm-fiber boundary bridge, without a hidden OAI assumption
2026-10-21; source-level extension after MERGED #998 and #999.

## 1. What is actually proved

In the companion file VF_919_NNS_NORM_FIBER_BOUNDARY_CORRESPONDENCE_20261021.lean:

1. Distinct marked and rescaled admission predicates partition a FINITE
   ORIGINAL LABEL carrier into mutually admitted, marked-only,
   rescaled-only, and absent faces. Complex coefficients are exactly
   retained. IMPORTANT: the rescaled coefficient is ALREADY SIGNED;
   there is no extra sign flip or an unsigned R+m confusion.

2. The exact Hermitian row/detector Gram retains the mixed A-B term.

3. For a finite labelled carrier S, a concrete map
   f : S -> (natural cofactor c, natural gap d=q-c), and arbitrary
   complex weights z, SUM_OVER_NORM_FIBERS proves exact recombination,
   including repeated ideal labels over one rational norm pair.

4. BOTH Cauchy-Schwarz stages are derived from Mathlib's finite
   CS and the ALREADY-COMPILED SignedHeight.card_le. Neither is supplied
   as a user assumption. Subject ONLY to the explicit and stringent
   canonical pair hypothesis

     for each a in S:
        SignedHeight.Admissible n H (f a).1 (f a).2,

   normFiber_lowGate_bridge_unconditional proves

     |sum_(a in S) z(a)|²
       <= (1+floor(H/n))
          * sum_(p in image f) card(fiber(p))
             * sum_(a in fiber(p)) |z(a)|².

   This is a strong source-admission interface, but not a new saving on
   every OpenAI detector column. It is an unconditional theorem in the
   sense that no moment/large sieve, arithmetic randomness, or CS
   premise is assumed; the canonical-pair admission property remains
   an explicit required input.

5. The scalar source decomposition of any row is

     F_u = A_u + B_u
     A_u = sum_(both gates) [marked(atom) + signed_rescaled(atom)]
     B_u = sum_(marked only) marked(atom)
           + sum_(rescaled only) signed_rescaled(atom).

   The complete energy is
     sum_u |F_u|² / D
       = [sum_u (|A_u|²+|B_u|²+2Re A_u conj(B_u))] / D.

## 2. Upstream source-grounded corrections to the proposed attack

The ORIGINAL source is:
* OAI.NumberTheory.DirichletL.Detector.Compensation.tupleOperation
* Detector.Physical.compensatedTuple_one
* Detector.GaussianCompensation.compensationSubsetCoefficient and
  compensatedPhysicalProbe_eq_subsets
* Moments.DetectorPlainFiberSource.detector_row_eq_source.

For a selected prime ideal P of norm q, the ONE-SLOT operation is
   star(eta(P)) * markedPhysicalProbe(D=P,X,Y,Z*q)
       - q^(-3/2) * physicalProbe(X/q,Y/q,Z).

For K slots, the actual J-subset atom contains
   (-1)^|J| * q_J^(-3/2) * star(eta(p_(J^c)))
and evals markedPhysicalProbe at
   X/q_J, Y/q_J, Z*q_(J^c).

The slot amplitude W_i(q_i/P_i) is COMMON outside the J-subset
sum. Window/shear claims based on an invented rescaled norm
U/P_ref do NOT describe the original source. No direct
per-column Cauchy/boundary payment is inferred from such a strip.

The markedPhysicalProbe is a theta/Poisson and Hecke row object,
NOT just mu_K(p*b) times a scalar log derivative and a dyadic
indicator. Squareful collisions do not automatically vanish from
the entire marked source because mu_K(p*b)=0 in a separate
ideal Mobius expansion. Collision claims need the exact inverse-
polynomial and row source.

## 3. Canonical rationals are a STRICT SUBCARRIER of norm fibres

For a prime ideal P in Z[omega], q=Norm(P) is not always a prime
rational integer:
* split p=1 mod3: prime ideal norm p;
* inert p=2 mod3: prime ideal norm p²;
* ramified p=3: norm 3.

The hCanon hypothesis requires ONLY the already-proved
factor-pair geometry: ordered positive factors (c,q) with q=c+d,
their product in the same square block, and bounded |q^2-c^2|/2.
It does NOT require q to be a rational prime or the largest prime.
In particular, q=4 (the norm of an inert prime ideal above 2)
with c=3 lies in the low-height geometric gate for n=3,H=4;
the companion Lean file certifies this example.

To use the *Möbius parity-toggle interpretation*, additionally
prove q=P_plus(c*q) is a rational prime, cofactor c is root-smooth,
q does not divide c in the relevant squarefree extension,
and the original masks/weights transfer. Such arithmetic assumptions
are not needed for the geometric Cauchy bound itself.

Use a disjoint partition:
  C_low = actual labelled ideal occurrences that satisfy all
          above canonical rational conditions;
  C_other = everything else, including all inert-norm primes,
            noncanonical highest-prime labels, and the high-height
            part of the selected windows.
The theorem controls ONLY C_low. No term is thrown away.
Inert norm p^2 can be in C_low if the geometric hCanon conditions
are satisfied; its OAI coefficient and Möbius meaning remain distinct.

The paper-level triangular root-boundary fibre count from #999
applies where q>R and the CANONICAL hypotheses hold, and does not
bound the entirety of the marked-only/rescaled-only physical
admission boundary. The projected integer-pair multiplicity must
be measured separately and retained, including selected-slot and
column generator multiplicity.

## 4. Why no high-sector improvement is claimed

The low bound does not control the full signed high-height
quadratic energy or the low/high mixed covariance. Separately
summing abs values would discard the mechanism we need.

To win ANY exponent, the next theorem must use the actual
marked-minus-rescaled, phases, source masks and physical Hecke
coefficients to show a quantitative power saving on the
unmatched and high-height source, uniformly in conductor,
row, derivative order, height and selected bands. This still
requires the original inverse/plain moments and large sieve.

Related native source already in the repository:
  research/oai_434/RHLeanActualEisensteinCompensatedSharpSquareBlock.lean
is an OAI 4.34.1 *source-algebra* sharp physical bridge with
actual ideals, but its preamble explicitly does NOT identify
the theta/Poisson detector with sharp-owner sum. That analytic
compatibility and any uniform signed moment are still open.

## 5. Acceptance & disproof tests before promoting this source

1. Kernel compile with warning fatal and printed axioms.
2. Confirm each original occurrence (selected primes tuple,
   J subset, ideal, row u) is carried ONCE and no norm collapse
   duplicates or deletes terms.
3. Confirm the Hecke phase, (-1)^|J|, q_J^(-3/2), physical weights
   W_i, W0/W1 and Z-rescaling are preserved.
4. Separate split/ramified from inert q=p² norms; never claim
   all ideal prime norms are rational primes.
5. Verify high-height and noncanonical residual are included
   explicitly in a full source equality.
6. Prove full marked/rescaled source equality before invoking
   an actual OAI detector fourth moment bound.

This is a framework for a REAL source-level weld. No
independent 7/8 theorem or RH improvement is claimed.
