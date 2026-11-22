# Native signed slope attachment and compiler repair checkpoint

22 November 2026. Current repair parent:
`baddf5afd886855a1c3600693573cd89dc85250e`.
The preceding signed-comparison checkpoint preserved contributor head
`46fb310c6e22478ae2a2cc1795ed8793acc14d5c`.

`descent_payment_ack=ALPOGE_NATIVE_DESCENT_PAYMENT_V1`
`tractability_ack=ALPOGE_VIOLE_TRACTABLE_RH_V1`

## Scope and proof status

This checkpoint implements the logarithmic forward-map reserve, the finite
signed slope comparison and its original scalar-window consequence in the
native namespace. It constructs the prescribed Hermitian spaces and full
inverse-ideal lattices with perfect integral trace forms, and evaluates the
short harmonic family using the literal lattice normalization.
It does not prove unconditional cancellation or supply the remaining
finite-adelic isometries, real complex structure, CM moduli, theta-cover,
actual section-germ realization, and geometric slope/metric estimates.
Hosted compilation of this complete repair batch is pending; both builds of
the preceding `baddf5a` head failed as recorded below.

The source remains
`CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.
The six finite source modules, their original hashes, and the native hashes are
recorded in
[`native_signed_slope_source_manifest.json`](../scripts/alpoge_geometric_source_audit/native_signed_slope_source_manifest.json).
All imported proofs are source code reconstructed in the native namespace.
No upstream terminal RH theorem or external compiled proof is imported.

## 1. The reserve is a forward-map statement

`NativeDescentCostPayment.lean` now proves, under the original size assumptions,

\[
E_0=3\log q_{\rm map}+2Cz^9\le b,
\qquad \mathcal H=2b-E_0\ge b.
\]

The exact collective squared-norm bill is
\(q_{\rm map}^3\exp(Cz^9)^2=\exp(E_0)\).
An additional positive factor \(F\) is absorbed when
\(\log F\le\mathcal H\). The specialized theorem retains the natural order
\(k\) and proves the payment for \(F=4^k\) from \(k\log4\le b\).
The accompanying joint-energy lemmas attach the paid scalar to an actual
forward-energy inequality.

These theorems do not change the lattice metrics, ranks, the already-spent
generator loss \(2\delta\Lambda=2b\), or the arithmetic observable. They do
not bound an inverse operator or its action on the dual recovery weight.

## 2. The finite comparison retains the signed arithmetic obligation

The finite assembly uses the original `Data` and eleven explicit inputs:
`HidaSetting`, `DIV`, `EComp5`, `HComp`, `Count5`, `Slopes`,
`QuotientSlopeBoundsWith`, `LossBounds`, `SlopeIneq`, `HHBound`, and `FParams`.
It proves

\[
\operatorname{umean}(\mathrm{ASK})
\le \operatorname{umean}(\mathrm{Main})+\mathrm{errorTermWith}.
\]

The intermediate proof first derives the signed estimate for `Ga` from the
divisor, counting, slope, and matrix-trace inequalities. The original
`LossBounds` then supplies `ASK − Ga ≤ LoP` and `IO ≤ LoP`. No hypothesis in
this finite assembly assumes a bound for the physical `ASK − MAIN`.

`StrongErrorBound.error_sizes` retains the full strong error-window premise

\[
(\bar\eta+4\sqrt{\bar e})x^{c_{HH}}b
\le Kx^\varepsilon(n_Ta),
\]

and proves

\[
\mathrm{errorTermWith}
\le x^{(e_{\rm Div}+e_{\rm Loss}+3)\varepsilon}
\left[n_Ta\left(1+\frac{m^2}{k}\right)+m(B_0+N_c)\right].
\]

The weak error-window predicate is not substituted for this strong premise.
The complete geometric error and the actual character divisor remain separate
until the existing native normalization theorem is applied.

The native attachment constructs the visible arithmetic fields from the complete
native ASK, the same widths and heights, the actual Euler constant and quadratic
log-derivative, and an equivalence with the actual CM-type place set. Its exact
identity identifies the original physical excess with the difference of these
two means. All geometric entries, including the finite-place gain `Ga`, remain
unchanged. The finite comparison then bounds that literal physical excess.
The original `B0` and `Nc` bounds give the full three-term bracket, and division
uses the positive earned character divisor. The resulting bound retains all
three native normalized geometric costs. These attachment proofs await hosted
verification; construction of their geometric suppliers remains open.

## 3. The remaining suppliers have concrete source locations

The source's divisor bridge uses `PBrDiv.mu_constant_of_blocks`: actual dual
rows identify the slope with the logarithmic covolume. It then uses
`AnalyticFirstToLatticeDiscriminant.divisibility_of_inner_divisibility`.
The actual family supplies placewise slopes, the family slope inequality and
size conditions in `ChainLatticeSizesModelEventually` and its reductions.
These require real rows, family, metrics, and cover realization.

Synthetic data-completion lemmas that begin by assuming
`ASK ≤ Main + error` are not suppliers for this task and are not ported.
Similarly, formal power-series evaluation alone does not construct the actual
polarized abelian scheme or canonical-connection section germs.

## 4. Repairs use complete hosted diagnostics

Both hosted builds of the exact parent `baddf5a` completed with failure and
reported the same diagnostic multiset, including cascading diagnostics:

| Build | Run | Job | Diagnostics |
|---|---:|---:|---|
| Native library | 45076126320 | 137373626091 | 53 errors, 25 warnings |
| Targeted closure | 45076126308 | 137373625258 | 53 errors, 25 warnings |

The repairs preserve both intervening contributor commits. The current batch
uses the canonical rational algebra in the private Galois helpers, registers
the exact existing `Pi.module` in the two cohomology definitions, and proves
the dyadic generator order through the actual additive equivalence. The
signed comparison fixes explicit width-sum instantiation, field projection
from local notation, the side of inequality addition, and the scalar
normalization equality. Further repairs address real/integer casts and the
algebra-homomorphism versus linear-map coercion in the harmonic span proof.
Warning cleanup removes only reported redundant simplifiers and marks five
unused binder names without removing any hypotheses. Existing construction
statements are preserved, with no heartbeat increase or gate change.

The earlier `46fb310` failures (44 errors and 36 warnings in each build) and
their repairs remain in the manifest history. Separate documentation,
inventory, atlas, export, cold-only and effective-resonance checks passed on
`baddf5a`; that does not make its failed Lean builds successful.

The root import manifest includes 1,481 native modules. The targeted
construction audit has 193 standard-axiom guards, including the new finite
source, scalar, lattice and evaluated-family results. Hosted warning-fatal
compilation remains the acceptance gate. Local Lean/Lake execution is not
used.

The earlier scalar audit and its 63-file hash ledger continue to describe
their historical source snapshot; this checkpoint does not rewrite that
evidence as if it had inspected later bytes.

## 5. Same-lattice normalization and the evaluated harmonic family

The follow-up construction supplies the literal lattice quantities used by
`ShortValAt`. A coprime denominator witness constructs the admissible odd
level `N = s*M`. Unimodularity and that actual level inclusion imply finite
generation and the hypotheses of the existing short-vector construction on
the same lattice. The denominator index and translation count satisfy

\[
\mathrm{zCard}=\mathrm{mIdx}\,
  [\Lambda:\Lambda\cap\mathcal O_E^n]^r.
\]

Both indices are proved positive under their original conditions. The
standard integral lattice is actually proved unimodular, and the native
inverse-ideal coefficient lattice has a finite level quotient.

The formal-jet construction retains the original directional derivatives,
ordered iterations, gauge, section-power parameter `N²`, and all four
normalizing factors. Fixed-degree linearity is proved, including the zero
polynomial. The already-constructed short integral harmonic family is
evaluated using the literal lattice index and translation count. Its
evaluation image spans the evaluation image of the full harmonic space.
The coefficient field remains independent of the CM host field.

This is not yet the identification with geometric cusp sections. The
actual polarized datum, level-function set, charts, section germs, choice
independence, and faithfully flat descent remain construction obligations.
The finite formula alone does not supply their Petersson or supremum bounds.

## 6. Actual selected-host scalar source

`nativeConstructedDyadicSignedSlopePayment` reuses the exponent function,
thresholds and prime-pair choice of `nativeConstructedDyadicGzPayment`.
The chosen pair precedes the subsequent scale variable, exactly as in the
existing theorem. The physical slope comparison is applied to its same
reciprocity map, inertia, Frobenius, canonical character constant, sharp
cutoff, `TT`, `T2`, heights and widths.

Writing \(C_{\rm Err}=e_{\rm Div}+e_{\rm Loss}+3\), the composed conclusion is

\[
\frac1T\sum_{t\in TT}G_z(a_t/b)
\le x^{C_{\rm Err}\varepsilon}
\left[
\frac{2a_E}{mb\Delta}\left(1+\frac{m^2}{k}\right)
+\frac{4nm x^\varepsilon}{T\Delta}
+\frac{2k x^{2\varepsilon}}{nT}
\right]+x^{1/2+\varepsilon}.
\]

No arithmetic witness is reselected between these inequalities. In
particular, the analytic remainder is the existing paid remainder; no
transport term is silently removed or charged a second time. The finite
slope hypotheses and strong windows apply to the same constructed physical
data. The scalar record update fixes `x`, `epsilon` and `b` to the actual
source parameters while preserving the geometric gain, slopes and errors.

`NativeGeometricCostWindows.lean` now reconstructs the original finite
arithmetic proof of `proposition_size_bound`, retaining all 15 meaningful
size conditions. It sets the error to the literal geometric bracket and
proves that error-budget premise by reflexivity. It does not assume a bound
on the physical excess or on the desired normalized conclusion. The exact
native character divisor is positive, and the complete normalization gives

\[
x^{C\varepsilon}\mathrm{NormalizedGeometricCosts}
+x^{1/2+\varepsilon}
\le x^{1/2+(C+3)\varepsilon}.
\]

The same selected-host theorem consequently returns both its full-cost
inequality and, under these original size windows,

\[
\frac1T\sum_{t\in TT}G_z(a_t/b)
\le x^{1/2+(e_{\rm Div}+e_{\rm Loss}+6)\varepsilon}.
\]

This is a conditional mean estimate. Its eleven physical geometric inputs,
strong trace windows, and `B0`/`Nc` estimates remain explicit. Their compatible
construction, a uniform choice of exponent constants before all subsequent
scales, and the actual window/pointwise transfer are still needed for an
eventual all-scale cancellation theorem. No unconditional RH conclusion is
asserted.

## 7. Prescribed Hermitian spaces and full polarization lattices

`NativePrescribedHermitianSpaces.lean` constructs the literal diagonal space
\(W_j=E^{k+m-1}\), its nondegenerate Hermitian form and the standard integral
lattice. Its Hermitian self-duality is proved directly. The negative-tail
coordinate permutation proves signature \((k+j-1,m-j)\) at every required
complex embedding.

`NativePrescribedPolarizationLattice.lean` identifies the source's literal
product span \(AA\,L_0\) with \((B^{-1})^{k+m-1}\), for the same actual
coefficient ideal. It proves finite projectivity over \(\mathcal O_E\),
localization to the full ambient space, and the exact ranks. Signed
coordinate duality constructs a perfect alternating integral form with

\[
\operatorname{EF}_j(x,y)_{\mathbb Q}
=\operatorname{Tr}_{E/\mathbb Q}\bigl(\xi h_j(x,y)\bigr).
\]

The form's map to the integral dual is bijective; alternation and conjugate
adjointness are proved. The native endpoint constructs one half-different
ideal \(B\) using `nativeDyadicHostRaw_principal` and uses that same ideal for
all \(j\). The ranks are \(k+m-1\) over \(\mathcal O_E\) and
\((k+m-1)(4\cdot2^e)\) over \(\mathbb Z\).

The next finite-adelic supplier is the source's `exists_adelic_neg_one`:
construct an element of \(E\otimes_F\mathbb A_f\) of relative norm \(-1\),
then use it for `dSpace_congr` and the graded-space isometries. It requires
actual local unit norm-solvability, completion instances and restricted
product patching. The separate `DomFor` supplier must construct the real
complex structure on this same lattice, prove positivity and compatibility
with every \(\mathcal O_E\) multiplication operator, and establish both
embedding-trace identities. The integral form above is not silently
identified with the source's later sign-selected form.

These constructions have source/hash manifests and independent static
reviews. Their next hosted build is still the proof-validation gate.

## 8. Acceptance status and next construction

```text
ROLE=Lean Verification
SOURCE=complete native signed ASK-MAIN and same selected-host Gz mean
WITNESS=actual CM host, prescribed W_j, literal AA*L0, exact integral trace form
MAP_PAYMENT=forward reserve implemented; actual geometric map suppliers remain open
NORMALIZER=Q=T*m*b*Delta/2 with actual TT/T2 positivity and all three costs
SIGNED_RECOMBINATION=physical signed gap retained; no inverse recovery weight used
FIRST_UNPAID=finite-adelic norm-minus-one isometries and full real DomFor construction
EVIDENCE=source reconstruction and independent static review; next hosted build pending
T_C_P=tractability progressed; mathematical novelty and unconditional proof not established
INDEPENDENT_APPLICATION=conditional finite slope stability and perfect integral lattice construction
FORMAL_STATUS=parent baddf5a failed; complete repairs prepared, standard-axiom gate retained
NEXT=construct local unit norm solvability and the actual real-tensor complex structure
```
