# #919 — Absorb OpenAI's compensated Hecke cancellation into actual VF C->R coordinates

**Status (Oct 9, 2026):** exact local compatibility partly already
kernel-proved in RH_Lean and extended by
VF_MID_919_OAI_FERMAT_TWIST_PROJECTION.lean.
The global character/physical-atom moment weld and new
power-saving estimates remain UNPROVED. This is a specific
mathematical integration plan, not an RH proof.

**New native-carrier extension:**
`VF_MID_919_OAI_PHASE_ALIGNED_OWNER_COMPENSATION.lean` now supplies
the phase-alignment condition, occurrence-preserving physical child return,
full admitted-plus-clipped cell reassembly, and its complete Hermitian Gram.
The precise scope and remaining arithmetic dictionary are in Section 8.

## 1. Distinguish TWO C-to-R maps. Only one preserves sextic phases.

**Invertible linear pair:** Define Fred's original
\[
\Phi(a+ib)=(a-b,a+b),\quad
\Psi(x,y)=\Phi^{-1}(x,y)=\frac{x+y}{2}
                                  +i\frac{y-x}{2}.
\]
Already formally proved:
- research/STABLE_FAR_PERRON_REALIFICATION.lean:
  stableFarRealPairToComplex_complexToRealPair,
  stableFarComplexToRealPair_realPairToComplex,
  stableFarRealPairNormalizedEnergy_complexToRealPair,
  stableFarRealPairNormalizedDot_complexToRealPair,
  stableFarComplexToRealPair_mul,
  stableFarRealPairNormalizedEnergy_realComplexMul;
- RHLean/Analysis/DistinguishedPrimeTransitionSupport.lean:
  complexRealPair_mul,
  restrictedPrimeTwoScalarContraction_iff_realPair.

The exact identities are
\[
 \frac{\|\Phi(z)\|_2^2}{2}=|z|^2,\qquad
 \frac{\Phi(z)\cdot\Phi(w)}2=\Re(z\bar w),
\]
and for \(m=a+ib\),
\[
 \boxed{\Phi(mz)=
   \begin{pmatrix}a&-b\\b&a\end{pmatrix}\Phi(z).}
 \tag{C1}
\]
For \(|m|=1\), the real matrix is a rotation and
retains *all* character phases and Hermitian energy.

**Squared-Fermat SCALAR map:** The paper also takes
\[
 \pi_{\mathrm{phys}}(z)=\Re(z^2).
\]
On the original Fermat/cofactor point
\[
 \Psi(c,q)=\frac{c+q}2+i\frac{q-c}2
\]
it satisfies
\[
 \boxed{\Re(\Psi(c,q)^2)=c\,q,\qquad
        \Im(\Psi(c,q)^2)=\frac{q^2-c^2}{2}.}
 \tag{C2}
\]
This is formally proved in RHLean.Geometry.ComplexSquareRecovery,
and literal ancestry product preservation appears as
RHLean.Proof.fermatSqReal_eq_sourceProduct in
RHLean/Proof/WheelToLedgerEquivariance.lean.

The squared scalar map is NOT injective:
\[
 \Re((-z)^2)=\Re(z^2).
\]
That identifies opposite sextic-character phases,
which is forbidden if one wishes to transfer the full
OpenAI phase-sensitive moment estimate. Use (C1)
through the character summation and ONLY THEN use (C2)
at physical endpoint reconstruction.

## 2. Exact character twist couples product and cofactor imbalance

Write \(m=a+ib\). From (C2), without approximation,

\[
\boxed{
 \Re((m\Psi(c,q))^2)
 =(a^2-b^2)cq
 -2ab\,\frac{q^2-c^2}{2}.
}
\tag{C3}
\]

This is NEW explicit formal theorem
RHLean.Geometry.vf919TwistedFermatProduct_eq_product_sub_gap.
The same source formally proves
vf919TwistedFermatProduct_one and
vf919TwistedFermatProduct_neg_phase.

If \(|m|=1\) and \(m=e^{i\theta}\), (C3) says

\[
 \Re((m\Psi)^2)
 = cq\cos(2\theta)-
   \frac{q^2-c^2}{2}\sin(2\theta).
\]

For sextic roots, \(m^2\) is a cubic root:
the projection can express a cubic-phase oscillation,
but by itself erases the sign distinguishing \(m\)
from \(-m\). The **factor-imbalance channel**
\((q^2-c^2)/2\) is not optional.

## 3. The exact Hermitian energy gap MUST be paid

Let \((x,y)=\Phi(z)\). Then:

\[
\boxed{
 |z|^2
 =\underbrace{xy}_{\Re(z^2),\ \mathrm{signed\ co-div}}
 +\underbrace{\frac{(x-y)^2}{2}}_{\mathrm{nonnegative\
 anti-diagonal\ energy}}.
}
\tag{C4}
\]

The real-squared physical product alone does not
upper-bound the Hermitian moment in OpenAI's proof.
For the genuine factor pair:

\[
\boxed{
 |\Psi(c,q)|^2=cq+\frac{(q-c)^2}{2}.
}
\tag{C5}
\]

The two formulas are NEW formal theorems
vf919ComplexNorm_sq_eq_signedProjection_add_antiDiagonal
and vf919FermatNorm_sq_eq_product_add_gap.
For example, c=1,q=101:
physical product cq=101; true complex energy=5101;
anti-diagonal gap=5000. Hence sending a far owner
directly into the scalar physical channel can
underestimate its analytic moment by a factor >50.

The existing zero-target covariance theorem
zeroTargetPairExcess_eq_realPart_realPairToComplex_sq
in research/ZERO_TARGET_MELLIN_FRESH_PRIME_SQUARE.lean
already identifies xy with
CoPartial(x,y)-Divergent(x,y). Its exact
Mellin fresh-prime sector matrix is
\[
 \begin{pmatrix}1+r^2&2r\\2r&1+r^2\end{pmatrix}
\]
with signed eigenvalue (1-r)^2 and unsigned
eigenvalue (1+r)^2. It has double signed zero
at r=1 without automatically destroying
the positive Hermitian energy.

**This is the exact missing energy weld:**
to control OAI's \(\sum |Z_u|^2\), one needs
BOTH the occurrence-preserving physical
Co-Div channel and a bound on the
anti-diagonal contribution. Strong
Co-Div cancellation alone is not enough.

## 4. OpenAI's local cancellation can be transported without loss

The preprint's exact compensated local
Euler identity (Eq 5.13b) has the form
\[
 \boxed{G_p+v_p^{-1}H_p=E_p},
 \qquad v_p=\chi_p(u),\quad p\nmid u.
 \tag{OAI}
\]
The displayed E_p is the paper's *specific*
holomorphic small local error including its
numerator and zero-extension conditions;
it is NOT set equal to zero.

Apply (C1) to obtain the EXACT real counterpart
\[
 \boxed{
 \Phi(G_p)+T(v_p^{-1})\Phi(H_p)=\Phi(E_p),
 \quad T(m)=
   \begin{pmatrix}\Re m&-\Im m\\\Im m&\Re m\end{pmatrix}.
 }
 \tag{C6}
\]

Since |v_p|=1 for p not dividing u, T(v_p^-1)
is a real rotation. No character phase,
complex norm, or mixed cross-owner interaction
is lost in this step. For p dividing u the
Hecke character has its natural ZERO, and
the paper handles the corresponding local
error separately; formula (C6) must not use
v_p^-1 for that row.

**Crucial analytic order:** C6 is a real-vector
equality but \(\Phi\) is NOT a complex-holomorphic
coordinate transformation in the variable s.
OpenAI's contour shifts remain on the original
holomorphic complex functions. Realify their
finite/quadratic moment expressions AFTER the
holomorphic identities, rather than shifting
contours of coordinatewise real parts.

## 5. What cannot be silently identified

- **Wrong owner order:** OAI selected-prime slots
  are disjoint and may be assembled as unordered
  tagged tuples. VF's canonical parent is
  obtained by stripping the LARGEST core prime.
  Native theorem
  sourceParent_eq_parent_iff_ordered
  in WheelToLedgerEquivariance.lean proves that
  a wheel fresh-prime insertion represents the
  canonical VF ancestry edge IF AND ONLY IF
  insertion is chronological (larger than
  all existing parent-core primes). Thus the
  OAI tuple must be sorted/tag-preserved with
  proof of exact multiplicities and zero masks.
- **Wrong source category:** OpenAI's
  coefficient phases belong to HECKE prime
  ideals in the Eisenstein integers
  Q(sqrt(-3)), not automatically to rational
  prime products pq. Rational split/inert
  prime-ideal channels and primary-generator
  orientation must remain as tagged data.
  Taking only the ideal norm can erase
  different sextic residues with the same norm.
- **Wrong physical weight:** The true original
  VF site weight w_floor(sqrt(pc)) depends on
  the WHOLE product pc. It is not generally
  a factorizable weight of owner p times
  cofactor c. OAI marked-minus-rescaled
  geometry changes the local physical
  square band and leaves exact boundary
  commutator terms. The signs and boundary
  terms must be retained before declaring
  the local Euler cancellation to hold in
  the native physical VF packet.
- **Wrong norm:** Re(z^2) and |z|^2 are
  different quadratic functionals, C4.
  One cannot substitute signed co/div
  for a positive large-sieve moment.

## 6. The actual open quantitative theorem

Start with ONE original full tagged physical
owner population (historical, returned,
late rank-two, live-3 and squareful, preserving
every occurrence exactly once). Give it
the full OAI Mellin/Hecke phases, local
compensation, and complete native VF weights.

Let \(\mathscr Z_u\) be its actual normalized
complex compensated character-row source
after all masks and endpoint corrections.
Set \((X_u,Y_u)=\Phi(\mathscr Z_u)\).
Prove the EXACT owner-to-OAI equality that
makes the following an equality on the
ACTUAL physical carrier:

\[
\boxed{
 \sum_{u\in\mathscr U}|\mathscr Z_u|^2
 = \sum_{u\in\mathscr U} X_uY_u
  +\frac12\sum_{u\in\mathscr U}(X_u-Y_u)^2.
}
\tag{GATE-2}
\]

For each fixed u this identity is pure
linear algebra (C4); the OPEN part is
constructing the true \(\mathscr Z_u\)
and identifying its signed quadratic
with the ORIGINAL Co-Div/age/owner
Sector Six Gram, including all cross
terms and first-bad signed historical
sources.

A meaningful improvement requires that
the **total right-hand side**, not just
its signed part, obey a NEW UNIFORM
power-saving estimate across ALL required
Hecke rows, conductor ranges and
frequency/scale parameters. In particular,
the anti-diagonal energy cannot be dropped.

Alternatively the new original physical
cancellation could lower the direct
reflected energy of OpenAI's compensated
probe before its final Cauchy inequality.
Either would require compatible low and
high continuation estimates to improve
the 7/8 zero-free boundary.

## 7. Established result vs open seam

**Already kernel-proved native:**
complex-real isomorphism, complex
rotation, exact Hermitian Gram,
Fermat product and imbalance,
Co/Div decomposition, fresh-prime
signed (1-r)^2 zero, and canonical
ordered-prime parent iff condition.

**Added in this PR:** C3, C4, C5
as warning-fatally compiled Lean
finite identities; exact phase loss
under scalar projection as Lean theorem.

**NOT proved:** an OAI sextic Hecke
character-to-VF physical-once-charge
dictionary, compatible local prime
compensation with VF moving root
weights, a new uniform quadratic/
higher character moment power saving,
or RH.

**Conclusion:** Yes, OAI's cancellation
can be absorbed *algebraically* and
Fred's C->R pair is the right
phase-preserving coordinate. The
physical squared-product projection
is the final decoder, not a replacement
for the complex analytic moment. The
most concrete new analytical target is
the native signed Gram PLUS its missing
anti-diagonal Hermitian energy, with
the genuine Hecke character phases
and physical owner weights attached.

## 8. Exact phase alignment on the existing physical owner cell

The new module works on the **existing first-separation owner carrier**
`lowOwnerFirstOwnerBaseFiber`, `lowOwnerFirstOwnerChildFiber`,
`lowOwnerFirstOwnerAdmittedBaseFiber`, and
`lowOwnerFirstOwnerClippedBaseFiber`. Its coefficient is exactly
`lowOwnerZeroFrequencyMobiusWeight R n`, the returned-core AMP
common-clock weight. This is not an assumed identification with the original
VF square-band weight or with the whole historical Sector Six source.
The owner here is the cell's first-separation prime, not a redefinition of
VF's greatest-prime ancestry convention.

Write

\[
 F_\chi(n)=w_R(n)\mu(n)\chi(n),\qquad
 \Delta_p(a)=(w_R(a)-w_R(pa))\mu(a).
\]

For an actual p-free parent, fresh-prime reversal gives
\(\mu(pa)=-\mu(a)\). If the row satisfies the explicit local law
\(\chi(pa)=\chi(p)\chi(a)\), the **unaligned** source is

\[
\boxed{F_\chi(a)+F_\chi(pa)
 =\chi(a)\Delta_p(a)
  +(1-\chi(p))w_R(pa)\mu(a)\chi(a).}
\tag{A1}
\]

Thus attaching the character to the physical sites before compensation
creates an extra term. It is not merely deterministic weight variation:
it can survive even for a constant site weight. For \(\chi(p)\ne0\),
the exact phase-aligned operation instead satisfies

\[
\boxed{F_\chi(a)+\chi(p)^{-1}F_\chi(pa)
 =\chi(a)\Delta_p(a).}
\tag{A2}
\]

The native compiled weight difference identifies
\(\Delta_p(a)=(D_a-R_a)\mu(a)\), with daughter crossing and root
crossing evaluated at the actual physical sites. No constant Mellin ratio
or factorization of \(w_R(pa)\) is needed.

The new theorem `vf919FirstOwnerChild_sum_eq_returnedParents` returns the
actual child population by \(n\mapsto n/p\), with inverse \(a\mapsto pa\),
for an arbitrary complex coefficient field. Every admitted occurrence is
preserved exactly once. Splitting the base fibre by whether \(pa\le R^2-1\)
then proves

\[
\boxed{Z_{R,p,\sigma}=I_{R,p,\sigma}+C_{R,p,\sigma},}
\tag{A3}
\]

where

\[
\begin{aligned}
Z&=\sum_{a\in\mathrm{Base}}F_\chi(a)
       +\chi(p)^{-1}\sum_{n\in\mathrm{Child}}F_\chi(n),\\
I&=\sum_{a\in\mathrm{Admitted}}\chi(a)(D_a-R_a)\mu(a),\\
C&=\sum_{a\in\mathrm{Clipped}}F_\chi(a).
\end{aligned}
\]

This is `vf919CharacterAlignedCell_eq_compensated_add_clipped`.
It requires only the stated local multiplicativity on the admitted fibre
and the nonzero prime phase, in addition to the native prime-parent laws.
At a zero prime phase the child site vanishes and the parent survives;
the module proves that separately. It does not replace OpenAI's analytic
ramified-row error with zero.

**Energy is taken only after A3.** Let \(W_{ab}\) be exactly
`weightedMoebiusFreshPrimeFourCornerMass
(lowOwnerZeroFrequencyMobiusWeight R) p a b`. Then

\[
\boxed{|I|^2=\sum_{a,b\in\mathrm{Admitted}}
               W_{ab}\Re(\chi(a)\overline{\chi(b)}),}
\tag{A4}
\]

and the complete physical cell moment is

\[
\boxed{|Z|^2=\sum_{a,b\in\mathrm{Admitted}}
 W_{ab}\Re(\chi(a)\overline{\chi(b)})
       +|C|^2+2\Re(I\overline C).}
\tag{A5}
\]

These are `vf919CharacterCompensatedInterior_norm_sq_eq_physicalGram`
and `vf919CharacterAlignedCell_norm_sq_eq_full_physicalGram`.
All ordered admitted cross terms are retained. The clipped square and
signed interior/clipped cross term are explicit and cannot be dropped.
At \(\chi=1\), the source specializes exactly to the native real
base-plus-child cell. The full cell also inherits the existing normalized
real-pair energy and signed-product-plus-anti-diagonal identities.

**What this narrows:** phase alignment and once-only child return are now
explicit native-carrier theorems. Transporting an OAI local row must prove
that its normalized coefficients implement A2 (or retain the A1 defect),
rather than asserting that twisting commutes with physical compensation.

**Still open:** identifying OAI's marked/rescaled ideal probe with Z,
including its \(q_p^{-3/2}\) scale changes, primary generator orientations,
zero extensions, fixed prime-slot supports and coefficients; attaching the
original VF moving square weights and all historical/cross-owner Sector Six
terms; and proving a new uniform bound on the complete resulting moment.
The presence of \(\chi(p)^{-1}\) in both A2 and OAI Eq. 5.13b is a useful
local compatibility condition, not a proof that their operators coincide.
No new zero-free boundary or actual-prime first-bad payment is proved here.

