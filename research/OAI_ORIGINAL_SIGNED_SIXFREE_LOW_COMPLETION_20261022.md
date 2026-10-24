# Genuine signed sextic low-row cancellation: primary, sixth-free, smooth radial carrier

Date: 2026-10-22. This note states an independent arithmetic result on an
EXACT carrier. It does **not** claim that original OAI's complete low
Gaussian source has already been identified with this carrier.

## The estimate (unconditional)

Let O=Z[omega], omega^2+omega+1=0, N(a+b*omega)=a^2-a*b+b^2.
Let m be an ideal coprime to (3), with q=N(m), and let chi be a
NONPRINCIPAL Hecke residue multiplicative character on O/m whose order
divides 6, extended by zero on nonunits. Real, cubic and genuine sextic
prime symbols from OpenAI are admissible. Define primary u to mean
u=1 modulo 3O, and sixth-free (u) to mean every ideal prime valuation
at most 5. Fix a C^1 radial weight W supported in [0,1], with bounded
supremum and derivative norm B.

For U>=1 put

    S6(U)= sum_{primary u, (u) sixth-free} W(N(u)/U)*chi(u).

Then there is an absolute constant C (depending only on geometry of O)
such that

    |S6(U)| <= C*B*(q*sqrt(U)+q^2*U^(1/6)).

This is a genuine SIGNED character estimate. It assumes neither
independent prime phases nor favorable NNS covariance, a zero-free
region, PNT, or RH.

### Full proof

1. Let L=3q. Since q belongs to m and 3 is coprime to m, the
   primary-masked function f(a,b)=1_(a=1 mod3,b=0 mod3)*chi(a+b*omega)
   is periodic with period L in each integer coordinate. Every
   complete L-by-L square tile contains equally many representatives
   of each class in O/m among the primary elements. Because chi is
   nonprincipal, its sum on O/m is zero. Thus the signed sum of f on
   EVERY complete tile is EXACTLY 0. Original OpenAI already proves
   the crucial primitive arithmetic fact as
   Moments/Unequal.lean::lifted_character_sum_zero.
   The new source-specialized Lean theorem
   original_lifted_nonprincipal_weight_variation bounds ANY
   nonuniform weighted tile by the absolute variation from a
   constant c, NOT by the total unsigned tile population.

2. First ignore sixth-free. For a tile containing support, choose
   an active point u0 and write W(N(u)/V) as
   W(N(u0)/V) plus its error. The first term sums to ZERO by step 1.
   Since N is a positive definite quadratic form and
   N(a+b omega)>=(a^2+b^2)/2, norm differences within an L-square
   are O(L*sqrt(V)+L^2). If L<=sqrt(V), the mean-value theorem
   bounds weight variation by O(B*L/sqrt(V)). The number of tiles
   meeting support is O((sqrt(V)/L+1)^2), each holding L^2 elements,
   so the exact weighted full-primary character sum is
   O(B*(L*sqrt(V)+L^2)).
   If L>sqrt(V), the trivial O(B*V) total lattice count is
   already <=O(B*L^2). This completes the uniform smooth-weight
   tile estimate. It does NOT estimate terms individually.

3. Since O is a PID, primary generators of ideals coprime to 3
   are unique: its six units map bijectively to (O/3O)^x.
   Sixth-free ideal inclusion-exclusion is EXACTLY
      1_sixfree(u)=sum_(d^6|(u)) mu_ideal(d).
   For primary generator delta of d, delta^6=1 mod 3O,
   N(delta^6*v)=N(d)^6*N(v), and chi(delta^6) is 1 if
   d is coprime to m (zero otherwise). Therefore S6(U) is a
   signed sum of complete-primary weighted character sums at
   V=U/N(d)^6 for N(d)<=U^(1/6). Apply step 2 to each: the total
   is at most
      C*B*[L*sqrt(U)*sum_d N(d)^(-3)
           +L^2*#{d:N(d)<=U^(1/6)}].
   Elementary counting of ideals in O gives a convergent
   sum_d N(d)^(-3) and #{d:N(d)<=T}=O(T).
   Substitute L=3q to prove the theorem.

4. At U=Z^(13/16), q=Z^(1/6), the two absolute source exponents
   are 55/96 and 45/96, compared with raw volume 78/96.
   Thus the proved relative power saving is 23/96 > 1/8,
   the number needed to move the original 3/16 LOW amplitude
   down to 1/16. This scale comparison is a CANDIDATE
   correspondence, not proof of the actual OAI low-source rate.

## How it hits the original OpenAI source

The FULL ORIGINAL indexedCompensatedHigh is an already-proved
Euler product of compensatedLocalCorrection factors, not an
imagined independent atom (see original
PrimeRows/MarkedCompensation.lean). On the genuine central contour
the actual unramified local factor is
   -star(idealRowHom(u,P))*idealUnramifiedCorrection
plus O((N P)^(-a)); the coherent sextic phase is the LEADING
UNIT-MODULUS piece. The local residual is NOT itself the whole
compensated source, so multiplying the small residuals across
slots is INVALID.

The leading phase across distinct fresh prime slots is a
nonprincipal sextic character of u modulo the product ideal
(including masks). Our estimate controls this leading phase
when accompanied by radial C^1 weights on the COMPLETE
primary sixth-free u-population. The source is not required
to be *probabilistically* balanced: exact residue tiling forces it.

Source admission still to establish: original physical test
weights and globalCorrection(u), inverse Hecke L factors,
the row-dependent conductor, finite selected masks,
derivative profiles and original D_U normalizer must be
reconstructed as superpositions of such complete-character
sums WITH sufficiently summable coefficients; at shifted
Re(w)<1, the original L expansion is not absolutely
convergent. An unproved source transfer is NOT a theorem.
The already-proved original low source enters a Cauchy
bound at Detector/LowActualEnergies.lean
(lowSeparatedIntegrand_source_cauchy), before this phase
structure can be used. That is the precise location
to attempt the signed source replacement.

## Audits

scripts/oai_sextic_sixfree_residue_completion_probe.py uses
genuine split Eisenstein moduli p=7,13,19; each
a+b*omega is tested in the primary congruence class and
tested for ACTUAL SIXTH-POWER divisor ideals. For each p
the complete 3p x 3p tile has EXACTLY equal multiplicities
in all six nonzero sextic phases. Weighted signed to
absolute ratios at increasing U are measured and printed.
This is evidence only; the bound above rests on the proof,
not the simulation.

Bottom line: an independent, quantitatively adequate
signed cancellation theorem is established for the
actual primary sixth-free sextic leading-character
carrier. Global OAI 3/4 and RH remain OPEN until
the full original physical-source admission is proved.
