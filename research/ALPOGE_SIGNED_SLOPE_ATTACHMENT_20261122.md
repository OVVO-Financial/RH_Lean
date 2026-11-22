# Native signed slope attachment and compiler repair checkpoint

22 November 2026. Parent: `46fb310c6e22478ae2a2cc1795ed8793acc14d5c`.

`descent_payment_ack=ALPOGE_NATIVE_DESCENT_PAYMENT_V1`
`tractability_ack=ALPOGE_VIOLE_TRACTABLE_RH_V1`

## Scope and proof status

This checkpoint formalizes the logarithmic forward-map reserve and reconstructs
the finite signed slope comparison in the native namespace. It does not prove
unconditional cancellation or supply the remaining CM moduli, theta-cover,
actual section-germ realization, and geometric slope/metric estimates.
Hosted compilation of these changes is pending; the preceding head failed.

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

Both exact-parent hosted builds completed with failure:

| Build | Run | Job | Diagnostics |
|---|---:|---:|---|
| Native library | 45070010686 | 137354713398 | 44 errors, 36 warnings |
| Targeted closure | 45070010715 | 137354728367 | 44 errors, 36 warnings |

The repairs preserve both intervening contributor commits. They address the
actual quotient/parent-projection instance inference, concrete Galois
composition elaboration, typed dyadic transports, one-based `TFAE.out` indices,
CM conjugation application, and integer absolute-value casts. Warning cleanup
removes only redundant simplifiers, no-op tactics, and compiler-reported
unused section instances. Existing construction statements and hypotheses
are preserved, with no increase in heartbeat limits.

The root import manifest and standard-axiom guards include the finite source
modules and the new reserve lemmas. Hosted warning-fatal compilation remains
the acceptance gate. Local Lean/Lake execution is not used.

The earlier scalar audit and its 63-file hash ledger continue to describe
their historical source snapshot; this checkpoint does not rewrite that
evidence as if it had inspected later bytes.
