# Native signed slope attachment and compiler repair checkpoint

22 November 2026. Current repair parent:
`a26fa375504cbd9d6bcbd0a32cf7b2f5c4daeb3d`.
The preceding `baddf5a` signed-comparison checkpoint preserved contributor head
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
the preceding `a26fa37` head failed as recorded below.

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

Both hosted builds of the exact parent `a26fa37` completed with failure and
reported the same diagnostic multiset, including cascading diagnostics:

| Build | Run | Job | Diagnostics |
|---|---:|---:|---|
| Native library | 45078081203 | 137379731321 | 20 errors, 18 warnings |
| Targeted closure | 45078081282 | 137379731509 | 20 errors, 18 warnings |

The repairs preserve both intervening contributor commits. The preceding batch
uses the canonical rational algebra in the private Galois helpers, registers
the exact existing `Pi.module` in the two cohomology definitions, and proves
the dyadic generator order through the actual additive equivalence. The
signed comparison fixes explicit width-sum instantiation, field projection
from local notation, the side of inequality addition, and the scalar
normalization equality. Further repairs address real/integer casts and the
algebra-homomorphism versus linear-map coercion in the harmonic span proof.
Warning cleanup removes only reported redundant simplifiers and marks five
unused binder names without removing any hypotheses. Existing construction
statements were preserved, with no heartbeat increase or gate change.

That hosted build successfully compiled `NativeDescentCostPayment`,
`AlpogeNativeSignedSlopeComparison`, `NativeGeometricCostWindows`, and
`NativeThetaJetEvaluation`. It did not complete the full construction audit:
the concrete Galois equivalence timed out, the cohomology quotient and framed
submodule still needed exact instance registration, and the prescribed
Hermitian-space and short-family proofs reported further elaboration errors.
The current repair batch addresses those exact failures. Its new local-norm
and real-tensor constructions have independent static reviews and await their
first hosted compilation.

The earlier `46fb310` failures (44 errors and 36 warnings in each build),
`baddf5a` failures (53 errors and 25 warnings), and their repairs remain in
the manifest history. Separate documentation,
inventory, atlas, export, cold-only and effective-resonance checks passed on
these preceding heads; that does not make their failed Lean builds successful.

The root import manifest includes 1,486 native modules. The targeted
construction audit has 221 standard-axiom guards, including the new finite
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

This is a conditional mean estimate. Its eleven original finite inputs,
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

The source's `exists_adelic_neg_one` supplier is now constructed as described
below. Its next consumer is `dSpace_congr` and the graded-space isometries.
The separate `DomFor` supplier must construct the real
complex structure on this same lattice, prove positivity and compatibility
with every \(\mathcal O_E\) multiplication operator, and establish both
embedding-trace identities. The integral form above is not silently
identified with the source's later sign-selected form.

These constructions have source/hash manifests and independent static
reviews. Their next hosted build is still the proof-validation gate.

## 8. Actual local norm solvability and real tensor realization

The local norm construction first proves representation of a unit by
\(s^2+Tst+Nt^2\) over a Henselian local ring with finite residue field and
unit discriminant. It proves the finite-field solution and both derivative
lifting cases. The subsequent completion theorem uses the literal
`v.adicCompletionIntegers K`: it derives maximal-ideal-adic completeness,
the Henselian property, surjectivity of reduction from the original integer
ring, and finiteness of the completion residue field. For a number field,
the original nonzero prime ideal supplies the required finite quotient.
Thus the endpoint constructs the norm-minus-one solution away from the
quadratic discriminant without a separate norm-solution, Henselian, or
finite-completion-residue premise.

`NativeDyadicAdelicNorm.lean` completes the actual global patching step. It
uses the same two Gauss roots and the same maximal real subfield. Outside
the primes over \(d\), it solves the integral quadratic norm equation for
\((1+\sqrt{-d})/2\). At primes over \(d\), coprimality makes \(q\) a unit;
the proof solves the \(q\)-equation and transports its coordinates using
\(\beta=\sqrt{-q}/\sqrt{-d}\) and \(\alpha=(1-\beta)/2\).
The exceptional set is proved finite, so the selected coordinates are actual
finite adeles \(S,T\). With the original integral half-root \(\theta\),

\[
y=\iota_{\mathbb A_f}(S)+\iota_E(\theta)\iota_{\mathbb A_f}(T)
\quad\text{satisfies}\quad\overline y\,y=-1.
\]

The scalar-extended involution is proved to be the same host conjugation,
and \(y\) is proved to be a unit. This is a finite-adelic tensor element;
it does not assert a global CM-field element with negative relative norm.
The diagonal GL congruence using this element is the next consumer.

The real-coordinate construction proves the source's exact map

\[
\theta:\mathbb R\otimes_{\mathbb Z}(B^{-1})^N
\longrightarrow\prod_{\tau\in\Psi}\mathbb C^N,
\qquad
\theta(a\otimes v)_{\tau,i}=a\,\tau(v_i),
\]

is bijective for the same native lattice and actual CM type. The canonical
embedding basis and the conjugate-complement identity prove scalar
bijectivity. The actual inclusion \(\mathcal O_E^N\subseteq(B^{-1})^N\)
then proves surjectivity on this lattice, and the already-proved exact
integer rank proves injectivity after real base change. One constructed
half-different ideal works for every prescribed rank. There is no independent
spanning or real-realization assumption.

The Hermitian convention is conjugate-linear in the first argument. The
subsequent source complex structure must therefore prove
\(\operatorname{EF}(Jx,x)>0\), and the second real trace identity has sign
\(-2\operatorname{Im}(\cdot)\). This convention is retained explicitly.
The real equivalence alone does not assert positivity or a completed `DomFor`.

The signed arithmetic input also remains distinct: `LossBounds` must come
from the actual family and signed-loss estimates. The new scalar comparison
does not manufacture that premise by changing `Ga`.

## 9. Acceptance status and next construction

```text
ROLE=Lean Verification
SOURCE=complete native signed ASK-MAIN and same selected-host Gz mean
WITNESS=actual CM host, prescribed W_j, literal AA*L0, integral trace form and real realization
MAP_PAYMENT=forward reserve implemented; actual geometric map suppliers remain open
NORMALIZER=Q=T*m*b*Delta/2 with actual TT/T2 positivity and all three costs
SIGNED_RECOMBINATION=physical signed gap retained; no inverse recovery weight used
FIRST_UNPAID=diagonal finite-adelic isometries and full real DomFor construction
EVIDENCE=source reconstruction and independent static review; next hosted build pending
T_C_P=tractability progressed; mathematical novelty and unconditional proof not established
INDEPENDENT_APPLICATION=conditional finite slope stability and perfect integral lattice construction
FORMAL_STATUS=parent a26fa37 failed; signed comparison/reserve/cost windows compiled, full gate pending
NEXT=use the constructed norm-minus-one unit for diagonal isometries and prove the real DomFor conditions
```
