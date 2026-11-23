# Geometric scalar audit: where an additional 4^k cost can be paid

**22 November 2026. Source inspection and paper derivation; no new Lean interface.**

Original source: `CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`.
Native construction inspected: PR #1194, commit `735a85c0c2e64a723bcdc08ba59a4259ad6ed176`.

`descent_payment_ack=ALPOGE_NATIVE_DESCENT_PAYMENT_V1`
`tractability_ack=ALPOGE_VIOLE_TRACTABLE_RH_V1`

## Finding

The source exposes an explicit **logarithmic map-height reserve**:

\[
\boxed{\mathcal H=2b-3\log q_{\rm map}-2Cz^9\ge b.}
\]

Here \(q_{\rm map}\) counts the actual integral character-trace maps,
\(e^{Cz^9}\) bounds multiplication by the same constructed regular section,
\(z=frL\), \(L=x^{\varepsilon_{\rm src}}\), and
\(b=e^{x^{\varepsilon_{\rm src}}}\). The consumer permits a collective squared
norm of \(e^{2b}\); the bounds used in its supplying proof actually yield at most
\(e^b\). Therefore an **additional proved squared-norm factor** \(4^k\) on those
same forward maps fits without changing the consumer whenever

\[
k\log4\le\mathcal H;
\qquad k\log4\le b\quad\text{is sufficient}.
\]

This is real numerical capacity in the original construction. It is not a
surviving \(4^{-k}\) theta multiplier, an inverse-coercivity bound, or a proof
that the proposed signed difference operator enters this norm comparison.
The counterexample \(c\ge4^k\) is a **lower** bound on an inverse constant;
it does not supply the upper bound needed to use this reserve.

The theta family constructing the auxiliary `cZero`-weight multiplier section
has differential order \(d_\theta\le z^7\), so its scale satisfies
\(d_\theta\log4\le b\).
That establishes capacity for a separately justified loss of at most
\(4^{d_\theta}\). The diagnostic order, the source rank, and this differential
order have not been identified. The degree bound is not a bound on every
main cusp-form weight or every Hilbert--Samuel jet.

The exact source commutator-coercivity theorem traced by the diagnostic has an
additional relevant feature: its numerical bound is discarded on its occurrence
consumer path. The all-place lattice descent uses integral injectivity, upper
operator norms, small generators, and near equality of ranks. It does not use
that inverse commutator constant.

## 1. Keep the parameters separate

| Symbol | Meaning in this audit | Relation supplied by the source |
|---|---|---|
| \(E\) | Actual CM host field | \([E:\mathbf Q]=2f\) |
| \(K\) | Coefficient field of the cusp lattices | \(K=Y.d.c_2.F\); not identified with \(E\) |
| \(d_K,s_K\) | Field degree and infinite-place count | \(d_K=2s_K\) for totally complex \(K\) |
| \(r\) | Actual Hermitian rank | \(r=k_{\rm src}+m-1\) |
| \(r_A,r_B\) | Ranks over \(K\) of the descent lattices | Integer ranks are \(d_Kr_A,d_Kr_B\) |
| \(q_{\rm map}\) | Number of character-trace maps | \(|\mathrm{grpHR}(fr)|\); not the arithmetic prime named \(q\) |
| \(L,b,z\) | Original scale data | \(L=x^{\varepsilon_{\rm src}},\ b=e^L,\ z=frL\) |
| \(n_\theta\) | Rank over \(E\) of the theta seed lattice | Selected as \(8(fr+1)\) in the short-span construction |
| \(d_\theta\) | Homogeneous polynomial degree / differential order | Source `DF`; distinct from \(n_\theta,r,k_{\rm src}\) |
| \(\kappa\) | Size of the actual weight | Sum of absolute `laOf` weights; not a jet order |
| \(k\) | Order or conditioning parameter in the diagnostic | No automatic identification with a source parameter |
| \(Q_{\rm char}\) | Earned arithmetic signal divisor | \(|TT|mb\Delta/2\), with \(\Delta=|T_2|/|H|>0\) |

Sources: [Scale and SizeData₂][scale], [CovolXOfCovol][covol-data],
[ShortSpanCompositionClosed][short-span]. The source's exponent is positive
and less than \(1/52\); it must be related explicitly to an eventual analytic
target epsilon rather than identified by notation alone.

## 2. The exact height and covolume definitions

Let \(A\) be a nonzero finitely generated \(\mathcal O_K\)-lattice, equipped with
the actual invertible Gram data. Write \(r_A=\operatorname{rk}_K A\) and
\(s=s_K\). `Formalism.HN` defines

\[
\begin{aligned}
\operatorname{ht}(A)
 &=2^{sr_A}|\operatorname{disc}K|^{-r_A/2}
    \operatorname{covol}_{\mathbf R}(A),\\
\operatorname{size}(A)
 &=\operatorname{ht}(A)^{1/(2sr_A)},\\
\mu_{\rm sq}(A)
 &=-2\log\operatorname{size}(A).
\end{aligned}
\]

The first two are definitions; the last is the `SizeMu` identity, with its
finite-generation, nonzero-lattice, totally-complex-field, and metric
hypotheses. More explicitly, the Euclidean slope in `Formalism.HN` obeys

\[
\mu_{\rm sq}
=2\mu_{\rm Eucl}-\log2+\frac{\log|\operatorname{disc}K|}{d_K}.
\]

The already normalized `GlobalTheory.AllWt.slope` is instead exactly
`slope_sq / 2`. These two ordinary-slope conventions must not be interchanged.
See [StatementPl][height].

Putting \(\operatorname{rd}(K)=|\operatorname{disc}K|^{1/d_K}\), the exact
normalizations become

\[
\begin{aligned}
\operatorname{ht}(A)
 &=\left(\frac2{\operatorname{rd}(K)}\right)^{d_Kr_A/2}
   \operatorname{covol}_{\mathbf R}(A),\\
\operatorname{size}(A)
 &=\sqrt{\frac2{\operatorname{rd}(K)}}\,
   \operatorname{covol}_{\mathbf R}(A)^{1/(d_Kr_A)},\\
\mu_{\rm sq}(A)
 &=\log\frac{\operatorname{rd}(K)}2
   -\frac2{d_Kr_A}\log\operatorname{covol}_{\mathbf R}(A).
\end{aligned}
\]

The normalized logarithmic covolume is

\[
\operatorname{lcv}(A)=\frac2{d_K}\log\operatorname{ht}(A),
\qquad
\boxed{\operatorname{lcv}(A)/r_A=-\mu_{\rm sq}(A).}
\]

These are the exact [lcv definition][lcv] and
[`log_covolume_slope_mu` identity][lcv-slope]. An apparent exponential in
degree or rank is already accounted for when the normalized root or logarithm
is taken. Increasing rank alone does not leave a free \(4^{-k}\) factor.

The source's matrix parameter uses the inverse metric convention: replacing
each matrix \(X_v\) by \(cX_v\), \(c>0\), scales actual norms by \(c^{-1}\)
and covolume by \(c^{-d_Kr_A}\). Equivalently, multiplying actual lengths by
\(\lambda>0\) multiplies size by \(\lambda\) and shifts the squared slope by
\(-2\log\lambda\). A rescaling must be transported through both lattices,
their maps, their integral structures, and the arithmetic comparison. It is
not an independently selectable geometric saving.

## 3. The actual map-height allowance and its reserve

For a map \(\Phi\) over the same field and Gram metrics, the source defines

\[
\operatorname{htMap}(\Phi)
 =\frac1{s_K}\sum_{v\mid\infty}
    \log\|\Phi\|_{\mathrm{op},v}^{\,2}.
\]

The joint target has the sum-of-squares norm. An estimate
\(\sum_h\|\phi_h f\|_v^2\le e^{2P}\|f\|_v^2\), at every place and for every
\(f\), supplies \(\operatorname{htMap}(\Phi)\le2P\).
This is [`htMap_le_of_points`][all-place], not an inverse-norm bound.

Consequently, an additional uniform factor \(4^k\) in a **squared** forward
norm bound consumes \(k\log4\) of logarithmic height. An additional \(4^k\)
in an unsquared norm would consume \(k\log16\). Neither conversion changes
the actual energy by itself.

### The complete original bill

The construction uses an integral regular cusp section \(u\), its translated
multiplication maps, and unnormalized character traces. Its exact collective
bill is

\[
\sum_h\|\phi_h f\|_\sigma^2
 \le q_{\rm map}^3M^2\|f\|_\sigma^2,
\qquad M\le e^{Cz^9}.
\]

The three powers of \(q_{\rm map}\) remain: two from the individual trace
norm bound and one from the number of target components. Dividing the traces
by the group order would require a new integrality argument.
See [`mapsCore` and `maps`][maps] and the native
[character-trace reconstruction](../RHLean/Geometry/NativeCharacterTraceMaps.lean).

The actual size suppliers give

\[
C\ge0,\quad \log q_{\rm map}\le45z^2,\quad
z\ge2C+200,\quad b\ge z^{12}.
\]

Set \(E_0=3\log q_{\rm map}+2Cz^9\). Directly from those bounds,

\[
\begin{aligned}
E_0
 &\le135z^2+2Cz^9\\
 &\le(135+2C)z^9\\
 &\le z^{10}\le z^{12}\le b.
\end{aligned}
\]

The stated source consumer allows \(e^{2b}\), leaving

\[
\boxed{\mathcal H=2b-E_0\ge b.}
\]

For any additional proved squared cost \(F>0\), the sufficient condition is
\(\log F\le\mathcal H\). In particular,

\[
k\log4\le b
\quad\Longrightarrow\quad
q_{\rm map}^3 e^{2Cz^9}4^k\le e^{2b}.
\]

This stronger intermediate estimate is a paper deduction from the inspected
source proof. The existing native
[`nativeDescent_collectiveNormBudget`](../RHLean/Geometry/NativeDescentCostPayment.lean)
retains the original \(e^{2b}\) conclusion. No new Lean theorem or interface
was added in this audit. Costs already incorporated into \(M\), including
the source's derivative and coefficient bounds, must not be charged a second
time.

## 4. What the theta normalizers actually cancel

The following factors belong to the same theta construction and must be
followed through their corresponding sums and metrics.

| Factor or stage | Exact compensation | Net effect in the inspected bound |
|---|---|---|
| Auxiliary level \(N^{-d_\theta}\) | Differentiating \(\theta(Nz)\) produces \(N^{d_\theta}\) | Coordinate-scale cancellation |
| Torsion-label factor \(|Q_{\rm level}|^{-1}\) | Sum has \(|Q_{\rm level}|\) terms | An average; no strict saving follows from the triangle inequality |
| Index and \(\beta^{-1}\) in the normalized branch | Same-index identities detailed below | Exact index cancellation |
| Raw theta reflex-ideal scalar | Cancels the raw \(\sqrt J\) loss | Leaves \([K:\mathbf Q]\operatorname{rd}(K)\) as a positive bound |
| \((2\pi\xi_R)^{-d_\theta/2}\) | Cancels the \(\pi t\) derivative scale, \(t=2\xi_R\) | Leaves \((e d_\theta)^{d_\theta/2}\) for positive order |
| Probability normalization of the Petersson measure | Total mass becomes one | A pointwise bound gives the same L² bound |

### Index identity

For the actual seed lattice, let

\[
I=[\Lambda:\Lambda\cap\mathrm{stdLat}],\qquad J=I^r.
\]

The source proves \(\mathrm{zCard}=\mathrm{mIdx}\,J\) and
\(|\sigma\beta|^2=J\), while the projected-vacuum bound contributes
\(B/\sqrt J\). Thus the normalized branch has

\[
J^{-1/2}\,\mathrm{mIdx}^{-1}
  (\mathrm{mIdx}\,J)\frac B{\sqrt J}=B.
\]

This is the literal
[`norm_index_cancellation_le_bound`][theta-index]. The raw branch takes
\(\beta=1\), so its bound instead retains \(\sqrt J B\); see
[`norm_rawThetaSeries_index_bound_le_sqrt`][raw-index]. These are two branches
using the **same** index, not two independent savings.

The genuine small scalar \(s\), chosen in the relevant inverse reflex ideal,
satisfies

\[
|\sigma s|\sqrt J
 \le e^{\operatorname{fieldSz}(K)}
 =[K:\mathbf Q]\operatorname{rd}(K).
\]

It removes the raw index growth while preserving the required integrality
conditions. It does not leave exponential decay. The Minkowski volume
comparison has \(2^c\sqrt{|\operatorname{disc}K|}<\pi^cR_{\rm Mink}^c\), with
\(c=d_K/2\). Here \(R_{\rm Mink}\) is a squared-norm budget; the proof uses
embedding radii \(\sqrt{R_{\rm Mink}/J}\). Taking the \(c\)-th root gives
\(R_{\rm Mink}>(2/\pi)\operatorname{rd}(K)\). That threshold is an algebraic reading of
the proof, not a newly certified sharper supplier. See
[`exists_small_scalar`][small-scalar].

### Archimedean metric and the surviving cost

The actual [`lieFac`][lie-factor] is

\[
\exp\left(-\frac{d_\theta}{2}\log(2\pi\xi_R)\right).
\]

The derivative estimate uses \(t=2\xi_R\), so for positive order,

\[
(\pi t)^{-d_\theta/2}
 (\pi e t d_\theta)^{d_\theta/2}
=(e d_\theta)^{d_\theta/2}.
\]

The source's raw estimate consequently has the form

\[
\operatorname{homN}(y_{\rm raw})
 \le\sqrt J\,\rho\,e^{9000z^2K_\theta}.
\]

After the scalar, integral denominators, flat twists, and full spanning-family
construction, the section multiplier is bounded by \(e^{Cz^9}\).
The native full expression retains component rank, coefficient-field degree,
root discriminant, group cardinality, coefficient norms, and the comparison
of pointwise and Petersson norms; see
[`NormPhiHatIndPhi`][raw-sup] and
[NativeSectionCostAbsorption](../RHLean/Geometry/NativeSectionCostAbsorption.lean).
The factorials in the polynomial spanning construction are costs, not
denominators supplying a hidden cancellation.

## 5. Quantitative capacity for the actual theta order

This calculation concerns the source's selected special weight
\(cZero\cdot hodgeWt\) for the auxiliary multiplier section \(u_{\rm sec}\),
with \(f\ge8\), \(r\ge100\), and the same chosen theta exponent. It does not
bound arbitrary main cusp-form weights. Put \(u=fr\). The source proves

\[
n_\theta=8(u+1),\qquad
K_\theta=d_\theta+\frac{n_\theta}{2}u,
\]

\[
K_\theta\le(1+r)S+u(4u+5),\qquad S\le u^5.
\]

The weight shift is essential: the source does **not** simply give
\(d_\theta\le S\). Its exact bound implies

\[
d_\theta\le u^6+u^5+4u^2+5u\le2u^6\le z^7.
\]

The middle inequality follows, for \(u\ge2\), from

\[
u^6-u^5-4u^2-5u
=u\bigl((u-2)(u^4+u^3+2u^2+4u+4)+3\bigr)\ge0.
\]

Since \(\log4<2\) and \(z\ge2\),

\[
d_\theta\log4\le2z^7\le z^{12}\le b.
\]

Thus the original scale has the concrete capacity

\[
\boxed{q_{\rm map}^3e^{2Cz^9}4^{d_\theta}\le e^{2b}.}
\]

Sources: [`sizeK_eq`][raw-sup], [`spanShortSize`][weight-size], the actual
choice in [ShortSpanCompositionClosed][short-span], and the special weight
bound in [ExistsShortIntegralVectorOfDeterminantBound][special-weight].
This paper deduction was independently checked during this audit. It is not
an upper bound on an arbitrary inverse-coercivity constant.

## 6. Why the rank and generator heights also matter

The all-place theorem requires genuine integral maps between the original
lattices, joint injectivity, Gram norms, finite generation, a nonzero source,
the collective bound \(e^{2P}\), and target generators of norm at most
\(e^\Lambda\). Its rank hypothesis is

\[
q_{\rm map}r_B\le(1+\delta)r_A.
\]

For \(\Lambda,\delta\ge0\) and \(t\le\mu_A-2P\), it concludes

\[
\boxed{t-\delta(|t|+2\Lambda)\le\mu_B.}
\]

The source applies this with

\[
P=b,\quad\Lambda=PP\kappa,\quad
\delta=\frac b{PP\kappa},\quad
t=-\mathrm{mainT}-(C_F+C_U)\mathrm{unitE}-2b.
\]

The generator-height bill is paid exactly:

\[
\delta(2\Lambda)=2b.
\]

Using the original size inequalities and ring-transfer loss gives

\[
-\mathrm{mainT}-(2(C_F+C_U)+9)\mathrm{unitE}\le\mu_{\rm core}.
\]

See [the original all-place theorem][all-place],
[MapsAt/RkAt/GminAt][covol-data], and
[`lowAt_of_cover`][lower-bound]. The native
[NativeAllPlaceDescent](../RHLean/Geometry/NativeAllPlaceDescent.lean) and
[NativeDescentCostPayment](../RHLean/Geometry/NativeDescentCostPayment.lean)
preserve these hypotheses and payments.

This mechanism needs both integrality and metric/rank information. The toy
example correctly refutes a uniform inverse bound from real injectivity
alone. It does not refute this stronger integral-lattice comparison.

## 7. Windows do not provide interchangeable exponential savings

### Literal widths

The actual scale definitions are

\[
a=xb,\quad X'=e^{x^{\varepsilon_{\rm src}/3}},\quad
b'=a/X',\quad w''=b'/(xn)=b/(nX').
\]

Thus \(b'/b=xe^{-x^{\varepsilon_{\rm src}/3}}\) and
\(w''/b=n^{-1}e^{-x^{\varepsilon_{\rm src}/3}}\). Under an explicit
physical identification \(x=R^2\), fixed \(0<\varepsilon_{\rm src}<1/52\),
and polynomial host size, this decay cannot offset a raw \(4^R\):
\(R^{2\varepsilon_{\rm src}/3}=o(R)\). This is separate from the much larger
logarithmic allowance \(b=e^{R^{2\varepsilon_{\rm src}}}\) before descent.

### Strong trace window

The source chooses

\[
E_8=e^{-x^{\epsilon/8}},\quad E_7=e^{-x^{\epsilon/7}},\quad
\bar\delta=E_7,\quad\bar\eta=6x^{-c_{HH}},\quad\bar e=2E_8^2.
\]

The actual trace input includes Hilbert--Schmidt matrix identities and
\(\eta_0,\eta_1\le E_8\), \(\sqrt{e_0}\le E_8\), and the required rank
comparison. Selecting widths does not establish those matrix conditions.
The strong-window transfer proves

\[
(\bar\eta+4\sqrt{\bar e})x^{c_{HH}}b
=\left(6+4\sqrt2\,x^{c_{HH}}e^{-x^{\epsilon/8}}\right)b
\le7b.
\]

The required `ErrWindows` comparison is against
\(K_0x^\epsilon|TT|a\). The full `errorTermWith` additionally retains
\((1-\bar\delta)^{-1}\le2\) under the original \(\bar\delta\le1/2\);
that factor is not part of the `ErrWindows` inequality itself.
See [SlopesFromSizeAndCount][trace-input] and
[AnalyticFirstToLatticeDiscriminant][trace-transfer]. There are three distinct
possible insertions of an extra factor:

| Where the extra factor enters | Resulting comparison |
|---|---|
| \(4^k\) multiplies squared error \(\bar e\) | Square root contributes \(2^k\); keeping the small term at most one requires \(k\log2+c_{HH}\log x+\log(4\sqrt2)\le x^{\epsilon/8}\) |
| \(4^k\) multiplies an already linear \(E_8\) term | Corresponding exponential comparison uses \(k\log4\) |
| \(4^k\) multiplies the whole trace contribution | It multiplies the nondecaying 6 as well; after cancelling \(b\), only \(K_0|TT|x^{1+\epsilon}\) is available |

For \(x=R^2\), \(k=R\), and a fixed analytic \(0<\epsilon<1/4\) as in the
source's `Inputs6dTo6c` range, the stretched-exponential small component cannot
absorb either indicated exponential loss. This analytic epsilon is distinct
from \(\varepsilon_{\rm src}\) until the same-scale bridge is supplied.
The whole trace term has only
polynomial room under the original polynomial host bounds. The pre-descent
height reserve cannot be applied to a different trace expression without a
proved transfer.

### BNBoundsU and the final divisor

Write \(n=|H|\), \(T=|TT|\), \(U=|T_2|\), and \(\Delta=U/n>0\).
The retained source windows give \(T,m,b>0\), so the divisor below is positive.
The original bounds retain

\[
B_0\le2nmbx^\epsilon,\qquad
N_c\le\frac{Uk_{\rm src}bx^\epsilon}{n(nx^{-\epsilon})}.
\]

The complete geometric bracket is

\[
B_{\rm geom}
=T a_E\left(1+\frac{m^2}{k_{\rm src}}\right)
+m\left(2nmbx^\epsilon+
\frac{Uk_{\rm src}bx^\epsilon}{n(nx^{-\epsilon})}\right).
\]

Dividing by the actual earned coefficient \(Q_{\rm char}=Tmb\Delta/2\) gives

\[
\frac{B_{\rm geom}}{Q_{\rm char}}
=\frac{2a_E}{mb\Delta}\left(1+\frac{m^2}{k_{\rm src}}\right)
+\frac{4nm x^\epsilon}{T\Delta}
+\frac{2k_{\rm src}x^{2\epsilon}}{nT}.
\]

The source also retains its outer \(x^{C\epsilon}\) loss and transport term
\(4/(\Delta x)\). With \(a_E=xb\), every \(b\) cancels; the permitted bound
\(a_E\le2xb\) only changes the first constant. No additional \(4^k\)
disappears here. The character remainder and complete signed ASK--MAIN
source must still be controlled on the same data.

Sources: [SplitInertia][bn-bounds], [ChTop][ch-top], [ChCore][ch-core], and
the native [cost normalization](../RHLean/Analysis/AlpogeNativeCostNormalization.lean).

## 8. The actual commutator-coercivity consumer

The inspected theorem is `GlobalTheory.T.commutator_coercive_on_annihilator`.
For a fixed matrix \(X\) and vector \(v\), it deduces

\[
\exists c>0\ \forall A,\quad Av=0\Longrightarrow
\operatorname{hs}(A)\le c\operatorname{hs}([A,X])
\]

from the corresponding injectivity condition. Its `hs` is the squared
Frobenius norm. The proof invokes finite-dimensional antilipschitzness;
it supplies no uniform bound on \(c\) across arbitrary \(X,v\).

The actual traced chain is
`EmbeddedFrames/Assembly.frame` -> `FrameF.frame` -> `WeightOccurrence/Occ`
-> `base_of_far_models_frame`. At its quantitative-consumer boundary the
source literally writes

```lean
obtain ⟨g, hg, -⟩ := hFr n ε d ε' d' e hG.fits hinjd hWd
```

and gives only \(g,hg\) to the far-parameter theorem. The third, coercivity
field is discarded on this path. The subsequent constants named `C` and `t₀`
are fresh witnesses from the `Far` theorem, which takes the retained trace
identity and no `Frame` coercivity argument. See [the frame assembly][frame] and
[BaseOfFarModelsFrame][frame-consumer]. This claim concerns this specific
theorem and its inspected consumers, not every theorem called coercivity.
The commutator theorem remains a formal proof dependency through the stronger
`Frame` proposition; discarding its numerical field does not erase that
dependency or prove the remaining source closure.

The native [two-by-two diagnostic](../RHLean/Analysis/AlpogePrimeFreeCommutatorConditioning.lean)
has fixed matrix dimension two for every conditioning parameter \(k\).
Its sharp \(4^k\) inverse constant therefore cannot be bounded by ambient
rank alone. Identifying that lower bound with an upper cost in `MapsAt`
would reverse the direction of the estimate and change the map being
estimated.

## 9. Consequence for the next construction step

The source already provides a precise candidate payment condition:

\[
\boxed{\log F_{\rm extra}+3\log q_{\rm map}+2Cz^9\le2b.}
\]

It can be used only after proving that \(F_{\rm extra}\) bounds the relevant
operation on the same constructed maps, metrics, integral lattices, and
rank comparison. If that operation changes the number of target maps or
their ranks, those costs must also be updated. Merely satisfying this
scalar inequality for unrelated data is insufficient.

The next obligation is consequently to locate a quantitative consumer that
actually needs the proposed commutator/jet cost and attach its operator to
the original construction. If the consumer discards the inverse constant,
no new uniform inverse-coercivity premise is warranted. If it uses it,
the required upper bound and its exact insertion point must be proved.

The current native construction still has substantive obligations at the
actual Hermitian spaces and finite places, moduli and uniformizations,
theta-to-cusp evaluation and spanning, good/deep covers, compatible Gram
lattices, rank shares, strong trace windows, and complete signed source
payment. This audit does not discharge them or establish
\(O(R^{1+\varepsilon})\) cancellation for the mock or arithmetic sequence.

### Evidence and publication

- **SOURCE_INSPECTED:** exact pinned definitions, map suppliers, theta
  normalizations, window comparisons, and the named commutator consumer.
- **PAPER_PROOF:** the reserve \(\mathcal H\ge b\), the actual-order bound
  \(d_\theta\le z^7\), and the conditional extra-factor payment. Separate
  auditors checked the height and theta-order calculations.
- **LEAN STATUS:** no Lean interface or source changed by this scalar audit;
  no local Lean/Lake execution. At report creation, the full native and
  targeted hosted builds of commit `735a85c` were still running; the
  separate static native audit had passed. These statuses do not certify
  the paper deductions as new Lean declarations.
- **T/C/P:** this is a concrete quantitative source audit and a decision
  about the next construction dependency. It does not claim a new
  cancellation principle or closure of the unconditional proof.

The companion [scalar ledger](data/alpoge_geometric_scalar_audit_20261122.json)
records inspected file hashes and the independent component audits.

**Subsequent compiler checkpoint.** After this audit, external compatibility
commit `bbcc8cabafc5766db4f1dad977b7a7345d51aa72` advanced PR #1194 and cancelled
the still-running `735a85c` builds. Their saved partial logs exposed further
compiler errors and owned warnings. The accompanying maintenance checkpoint
preserves that external commit and repairs those concrete diagnostics; it
does not introduce the proposed coercivity interface or a new scalar axiom.
The 63-file ledger remains a historical fingerprint of the revisions actually
inspected for the mathematical audit. Compilation of subsequent repairs is a
separate hosted verification obligation.

[height]: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/HarderNarasimhan/StatementPl.lean
[lcv]: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/QuotientMetricDivisors/Statement.lean
[lcv-slope]: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/MeanHeightDescent/AverageDegreeBounds/CovolumeAssemblyHolds.lean
[all-place]: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HtMapLeOfPoints.lean
[maps]: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapsBoundOfDeepGood.lean
[scale]: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/LocalRingCardinality/DataParams₂.lean
[covol-data]: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AbelianVarietyTheory/Definitions/Divisors/CovolXOfCovol.lean
[lower-bound]: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LowerBoundOfAllEstimates.lean
[theta-index]: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/NormShortGeneratorEvalLeOrthonormalFrame.lean
[raw-index]: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormRawThetaSeriesIndexBoundLeSqrt.lean
[small-scalar]: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSmallScalarReflexIdealSelfDualLattice.lean
[lie-factor]: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/LocalToGlobal/ProjectiveLattices/NormsFree.lean
[raw-sup]: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormPhiHatIndPhi.lean
[weight-size]: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ThetaWeightAndFlatExponentSizeBound.lean
[short-span]: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/HodgeBundleWeights/ShortSpanCompositionClosed.lean
[special-weight]: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/HodgeBundleWeights/ExistsShortIntegralVectorOfDeterminantBound.lean
[trace-input]: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/SizeWindowBrackets/SlopesFromSizeAndCount.lean
[trace-transfer]: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/SizeWindowBrackets/ChainSlopeWindows/AnalyticFirstToLatticeDiscriminant.lean
[bn-bounds]: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/DedekindLFunctions/SplitInertia.lean
[ch-top]: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChTop.lean
[ch-core]: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean
[frame]: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/WeilBound/RepresentationTheoryGL/HolomorphicDiscreteSeries/EmbeddedFrames/Assembly.lean
[frame-consumer]: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/WeilBound/RepresentationTheoryGL/HolomorphicDiscreteSeries/HarishChandraDescent/IntegerLowerBounds/BaseOfFarModelsFrame.lean
