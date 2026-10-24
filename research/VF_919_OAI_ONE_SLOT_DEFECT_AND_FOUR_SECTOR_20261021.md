# One-slot OAI source audit: exact scale match, conditional log model, missing physical identification

**2026-10-21. Research follow-up to draft #1000. Lean 4.34.1.**

## 1. Verified source: what the upstream one-slot operator actually says

OpenAI file:
  openai/math/lean/OAI/NumberTheory/DirichletL/Detector/Physical.lean

The theorem compensatedTuple_one states, literally,
  F(p) = star(eta(p)) * markedPhysicalProbe(D=(p),X,Y,Z*Norm(p))
        - Norm(p)^(-3/2) * physicalProbe(X/Norm(p),Y/Norm(p),Z).

The markedPhysicalProbe sum contains:
* ideals s with selected excluded-prime masks,
* W1(Ns/Y),
* primaryGenerator and idealRowHom,
* residue, Gauss sums, a sqrt(physical-normalizer),
* W0(Nm/(Nc*Ns*X)),
* an actual vertical Mellin integral of a spectral row with
  D-dependent coefficient and Z-rescaling.

The selected-prime window is OUTSIDE the finite J-subset sum in
GaussianCompensation.compensatedPhysicalProbe_eq_subsets, and its
true coefficient is
  (-1)^|J| * Norm(p_J)^(-3/2) * star(eta(p_(J-complement))).

The source does NOT display the proposed (k+1)^(-1) selected-owner
weight, nor does it use an invented P_ref for the X/Y rescaling.

For U>0,q=Norm(p)>0,c=Norm(b):
  c/(U/q) = q*c/U = Norm(p*b)/U.
This is an EXACT pointwise equality of one candidate norm-window
argument. It does not identify the FULL Gaussian/Mellin physical
coefficients, row masks, phases, Z parameters or the separate W0/W1
admissions. In particular, the primitive physicalProbe does not
literally take the user's proposed single scalar W(N(pb)/U) as
its only window.

## 2. Conditional logarithmic model: precisely what it proves

Let
  r_j = w L_b^j
  m_j = -w/(k+1) (L_b+L_p)^j,
where L_b=log Norm(b), L_p=log Norm(p), and k counts selected
primes occurring in b. Here m_j is a CHOSEN model, not a
source-extracted identity from the actual physical probe.

Then the model gives the exact algebraic formula

  r_j + m_j
    = [k/(k+1)] w L_b^j
      - [w/(k+1)] ((L_b+L_p)^j-L_b^j).

Therefore:
* j=0,k=0: r_0+m_0=0 in THIS model.
* j=1: log-shift term = -w L_p/(k+1).
* j=2: log-shift term = -w(2 L_b L_p+L_p^2)/(k+1).

The Lean module compiles these identities, deliberately named
MODEL_* to prevent treating them as actual OAI source theorems.

Restore an unproved relative complex multiplier gamma in the marked
coefficient:

  m_j(gamma)=-gamma*w/(k+1)*(L_b+L_p)^j.

Then the exact j=k=0 residual is

  r_0 + m_0(gamma) = (1-gamma)*w.

For gamma=-1 and w=1, the result is **2 rather than 0**.
Identical scalar window arguments do not establish gamma=1.

One must prove the equality of full marked and normalized rescaled
physical coefficients, not assume it from arithmetic multiplicativity.
An elementary exact one-slot equality condition is

  star(eta(p))*Marked = Norm(p)^(-3/2)*Rescaled.

The original OpenAI local factor NORMALIZED CANCELLATION, in
Detector/Local.lean, produces a nontrivial remaining error numerator,
NOT a pointwise zero. Its successful proof estimates that error
across characters/heights/moments rather than declaring it absent.

## 3. Source sectors without lost ideal labels

The Lean four-sector classifier takes an arbitrary FINITE ORIGINAL
LABEL carrier S with predicates collision, inert, lowGeom. It gives
disjoint priority sectors, reconstructing the full sum exactly:

  S = collision
      disjoint-union noncollision-inert
      disjoint-union noncollision-noninert-lowGeom
      disjoint-union noncollision-noninert-not-lowGeom.

The fourth sector retains ALL remaining high/noncanonical/masked
labels. It is not assumed small. Collision precedence handles
possible overlaps instead of double charging. The user-proposed
four-way decomposition is thereby certified only as a
mathematical index partition, not as a complete physical source map.

The lowGeom predicate must come from actual
SignedHeight.Admissible along a VERIFIABLE labelled map to an
integer cofactor/gap pair; merely knowing rational norms does
not guarantee it.

## 4. What conditional support counting can and cannot supply

* Eisenstein prime ideals: split p congruent 1 mod 3 yield
  2 ideal labels of norm p; ramified p=3 yields 1; inert
  p congruent 2 mod 3 yields 1 label of norm p^2.
* For a SINGLE one-slot P,b carrier without extra row/slot
  multiplicity, a rational norm pair (c,q) in the split/ramified
  sector has at most 2*tau(c) distinct ideals. Additional OAI
  character and selected-tuple indices require their own factors.
  The #1000 bridge uses the ACTUAL measured fiber cardinality,
  not the guessed tau envelope.
* Inert ideal-prime counts in [P0,2P0] are <=sqrt(2P0)
  trivially, and O(sqrt(P0)/log P0) for large P0 by PNT,
  but count sparsity is not a character-moment saving if
  the source amplitudes or correlations grow.
* In a SIMPLIFIED norm dyad m=pb with p|b and b=p*b'
  implies Norm(b') ~ U/Norm(p)^2. This gives a smaller
  *candidate site range*; the actual markedPhysicalProbe is
  NOT an ideal-Mobius convolution with every collision killed
  by mu_K(pb)=0. One must prove the source-specific term and
  any collision saving.

**Caution about the geometric root lemma:** #999's finite
canonical height count is PURE ordered-factor geometry. It does not
require Norm(p) itself to be a rational prime. An inert norm p^2
can still be geometrically admissible, although it cannot be
treated as rational largest-prime Möbius parity without further proof.

## 5. The next genuinely arithmetic theorem, still open

1. Extract a literal indexed finite source from
   compensatedPhysicalProbe_eq_subsets or detector_row_eq_source,
   preserving u, ideal I, p selected tuple, J subset, physical
   W0/W1, Z, character and normalizer.
2. PROVE an injective/finite-fiber correspondence pairing the
   marked and rescaled physical coefficients, not only their
   rational norm arguments.
3. Show the actual normalized coefficient has a common amplitude
   w with a certified relative gamma and (if relevant) the
   (k+1)^(-1) owner normalization. Otherwise use the actual
   weights and retain gamma-1 defect explicitly.
4. Apply #1000 low-height cardinal and actual fiber sizes only
   on the projected admissible subcarrier. Retain inert,
   collisions and all high-height/masked residuals.
5. Obtain an independently proved uniform signed moment saving
   for those ORIGINAL physical coefficients and preserve all
   mixed NNS Co/Div cross terms. Neither the scalar identity nor
   inert-count sparsity produces this analytic payment.

**Status:** finite exact-window, conditional logarithmic algebra and
four-sector partition formalized and subject to own warning-fatal CI.
**Not proved:** actual-source pointwise j=k=0 annihilation; K-slot
multi-selected owner normalizer; full source identification;
high-sector moment power saving; RH/new zero-free exponent.

Existing input:
  #998 original-source NNS finite Gram identity (merged)
  #999 canonical low gate (files restored in #1000)
  #1000 actual labelled norm-fiber Cauchy bound (draft)
  openai/math Detector/Physical.lean, GaussianCompensation.lean,
  Local.lean, CompensationActual.lean
