# Exact finite Galois-cochain / NNS / Fourier / real-integral bridge
Date: 2026-11-21. Finite-level arithmetic theorem. NOT an RH proof.

## Precise mathematical object

Fix a finite Galois quotient Gamma and a finite abelian Gamma-module A;
for an Alpoge finite torsion level, A=Z/(p^r)(-e) with actual cyclotomic
action rho. For each local place v choose H_v <= Gamma, the IMAGE of the
full local decomposition group. Inertia alone is not enough.

A normalized global cochain f:Gamma->A satisfies f(1)=0.
Introduce one local witness b_v in A for each v and define

  L(f,(b_v))(g,h) = f(gh)-f(g)-rho(g)f(h)
  L(f,(b_v))(v,h) = f(h)-(rho(h)b_v-b_v), h in H_v.

This is a group homomorphism from X=C1( Gamma,A ) + product_v A
to Y=C2(Gamma,A) + product_v C1(H_v,A).
The first equations are the genuine global cocycle relations;
the second equations are the genuine local coboundary restrictions.

Define Zloc = global cocycles locally coboundary at every v;
B1 = {d0(a): a in A}, d0(a)(g)=rho(g)a-a.
The **finite-level** Sha group is Zloc/B1.

## The exact arithmetic-to-Sha theorem

THEOREM:
  |Sha1(Gamma,A; H_v)| = |ker L|*|A^Gamma| /
                           (|A|*product_v |A^(H_v)|).        (1)

PROOF: Projection ker L -> Zloc is surjective. Its fibre over a
cocycle f is the product of cosets of ker(d0_v)=A^(H_v).
Thus |ker L| = |Zloc|*product_v |A^(H_v)|.
Also ker(d0)=A^Gamma, so |B1|=|A|/|A^Gamma|.
Every global coboundary is locally a coboundary. Consequently
|Sha1|=|Zloc|/|B1|, proving (1). No determinant is used.

For A=Z/(p^r), the normalized cochains have cardinality
p^(r*(|Gamma|-1)), so the unconditional finite-level bound is
log |Sha1| <= r*(|Gamma|-1)*log p.
This is NOT a uniform RH-strength bound when Gamma and r vary.

## EXACT complete-character equivalence using native Alpoge detector

Let Y^ be all additive characters of the finite abelian group Y.
For every x in X,

  1_(Lx=0) = (1/|Y|)*sum_(chi in Y^) chi(Lx).

This is EXACTLY RHLean.Analysis.alpogeNativeCharacterDetector,
instantiated with finite host Y, a=Lx and g=0. Thus

  |ker L| = (1/|Y|)*sum_(x in X)sum_(chi in Y^) chi(Lx).
          = (|X|/|Y|)*|ker L^dual|.                         (2)

The same complete source L appears on both sides.
The accompanying Lean theorem nnsFiniteRelation_fullCharacterDetector
reuses the existing detector directly, and does not assume a source
estimate. Its companion NNS theorem records the target-free signed
UPM1-LPM1 reassembly.

## NNS discrete integral -> ordinary integral, a.s.

Choose an enumeration X={x_0,...,x_(N-1)} and define
k_j=1_(L x_j=0). This is exact integer arithmetic.

For ANY real NNS target tau,

  |ker L| = UPM1(k-tau)-LPM1(k-tau)+N*tau.                  (3)

At tau=1/2, UPM1=|ker L|/2 and
LPM1=(N-|ker L|)/2, so both signs survive.

Define the step function H(t)=k_(floor(Nt)) on [0,1),
arbitrary at t=1. Then exactly,

  integral_0^1 H(t) dt = |ker L|/N.                         (4)

Substituting (4) in (1) yields the genuine finite-level
cohomology-to-real-integral identity

  |Sha1| = N*(integral_0^1 H)*|A^Gamma| /
              (|A|*product_v |A^(H_v)|).                   (5)

H is not continuous at its finitely many jumps. The continuous
integral mean-value theorem must not be applied at those jumps.
Inside each constant segment, the mean-value identity is exact;
piecewise-linear continuous approximants obey the usual MVT and
converge to H in L1. More strongly, H has total variation <=N-1.
Any tagged uniform Riemann sum Q_n with cell width 1/n obeys

  |Q_n - integral_0^1 H| <= (N-1)/n.                        (6)

This holds for ALL cellwise tags and therefore almost surely under
any law of valid random tags, without iid or independence assumptions.
For an aligned mesh and interior tags the quadrature is exact.

## Exact modular tests

The executable modular checker enumerated normalized cocycles,
local witnesses and global coboundaries independently, then compared
those counts to formula (1), checked the Fourier annihilator identity
(2), the exact rational NNS identities (3), and (6).

  Gamma | A   | action  | local group | |ker L| | |Sha1|
  C2    | Z/2 | trivial | {0}         |   4     |   2
  C2    | Z/2 | trivial | C2          |   2     |   1
  C3    | Z/9 | trivial | {0}         |  27     |   3
  C3    | Z/9 | trivial | C3          |   9     |   1
  C2    | Z/3 | sign    | {0}         |   9     |   1
  C2    | Z/4 | sign    | {0}         |  16     |   2

These are finite-group-cohomology examples, NOT claims about a
particular realized Alpoge number field.

## Precisely what the existing repo still does not identify

RHLean has:
- native Alpoge Frobenius/inertia finite-additive-group means and the
  complete additive-character detector,
- exact signed Mobius/von-Mangoldt/ASK/Gz sources,
- NNS first/second partial moments and C->R integral lattice transport.

The original Alpoge formalization has the ACTUAL global cohomology and
local restriction definitions (Formalism/GaloisCohomology/Statement.lean)
and the class field/cyclotomic maps:
UpperTheory.V.Kum.resInfInj, resInfMem, pullEq, shaLen_le_of_cl.

BUT RHLean's current Frobenius host accepts arbitrary
  inertia: Nat -> AddSubgroup G
  frob: Nat -> G.
Neither an arbitrary finite host nor its scalar character means
automatically supplies the genuine cochain representation, decomposition
subgroups and local restriction maps for the realized fields and twists.

The same-source diagram to prove next is:
(actual field K, p, e, Galois action rho, decomposition maps)
 -> actual finite cochain operator L
 -> native full character projector (2)
 -> native NNS signed integral (3)
 -> ordinary convergent integral (5).

An exact identification of this L-dependent Fourier population with
the ORIGINAL PHYSICAL prime-power ASK/Gz population is still separate.
In particular finite cohomology identities alone DO NOT prove RH or
its uniform estimates. Do not silently replace the physical source.
