# Native integral descent and complete character-source payment

## Status and scope

This attack starts from native main `608b5702a20ab34a9efcd38b5d59e09f9f565f61` and reads the original geometry at `CocoSgt/riemann-hypothesis-lean@7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`. The proof changes are in [PR #1193](https://github.com/OVVO-Financial/RH_Lean/pull/1193). Its exact-head hosted checks determine formal acceptance; no local Lean execution is used.

The native results implemented here are finite integral descent with constructed completion vectors, one-sided full-source width payment, and a complete character-source comparison with a derived divisor. **The source-compatible theta/cusp lattice family and the final critical estimate remain open in RH_Lean.** The finite comparisons below do not claim that their remaining physical source is small.

The decisive arithmetic statement now has a more explicit form. Write:

- $Z$ for the original subgroup average of the full physical ASK−MAIN over actual heights and rows;
- $L_{\rm thin}$ for its literal signed complement after selecting the thick colours;
- $Y_K$ for the retained character sum at the original heights $a_t/b$ and original phases;
- $\Sigma_K$ for the explicitly defined norms of the excluded character terms;
- $T=|TT|$, $n=|H|$, $\Delta=|T2|/n$, and $Q=Tmb\Delta/2>0$.

If the actual thick widths lie in ([b,b+h]), all physical widths are positive, the original sharp cutoff is valid, and $a_t/b\le X$, the native theorem is

\[
Y_K\le \frac{Z-L_{\rm thin}}{Q}+\Sigma_K
 +\frac{4h(\log4+2)X}{b\Delta}.
\tag{1}
\]

The width term in (1) is paid from the actual all-prime-power arithmetic. The other terms are retained, not asserted to meet the critical exponent. The full annihilator projection is also available before any character is excluded; an absolute-value charge is optional and is not a replacement for signed recombination.

The remaining global task is to construct and estimate **one common realized family** so that the entire right-hand side of (1), including the geometric source, the signed thin return and the character correction, has the required root-scale bound. The variable-height character signal must then be transferred to the appropriate analytic consumer. It is not silently identified with scalar $G_z(R^2-1)$.

## 1. An actual finite integral descent theorem

See [NativeFiniteIntegralDescent.lean](../RHLean/Geometry/NativeFiniteIntegralDescent.lean) and [NativeIntegralCompletion.lean](../RHLean/Geometry/NativeIntegralCompletion.lean).

Let $A\subset U$ and $B\subset V$ be Euclidean integral lattices with fixed metrics and integral bases, of ranks $r>0$ and $N=r+d$. Suppose:

1. $f:U\to V$ is an injective linear map with $f(A)\subseteq B$;
2. $\|f(x)\|\le e^P\|x\|$ for every $x\in U$;
3. $S\subset B$ spans $V$ over $\mathbb R$, and every vector of $S$ has norm at most $e^\Lambda$.

There is no slope or arithmetic-source estimate among these hypotheses.

### Construct the completion

Extend the independent family $f(a_1),\ldots,f(a_r)$ to a real basis using vectors from
\(\{f$a_i$\}\cup S\). Exactly $d$ additional vectors $w_1,\ldots,w_d\in S$ are needed. Their bounds survive unchanged. The theorem does not assume that $S$ contains a short integral basis.

Express the whole completed frame in the original integral basis of $B$. Its coordinate matrix $C$ is integral and has nonzero determinant. Both the matrix and its nonsingularity are constructed from the supplied map, integrality and spanning set.

### Retain the source metric

A product of lengths of the original source basis would lose its angles. Instead extend the map to
\[
F:U\oplus\mathbb R^d\longrightarrow V,
\qquad F(x,y)=f(x)+\sum_j y_jw_j.
\]
Use the original metric on $U$ and the ordinary orthogonal metric on the auxiliary factor. The auxiliary standard lattice has Gram determinant one.

In an orthonormal basis of the domain, the actual image columns are $f(u_i)$ and $w_j$. Hadamard bounds their product. No estimate for the norm of the entire extended map is required, and no dimension factor is introduced. Exact Gram transport retains the original source determinant:

\[
(\det C)^2\det\operatorname{Gram}(B)
\le
\det\operatorname{Gram}(A)\,
e^{2rP+2d\Lambda}.
\tag{2}
\]

Since $C$ is a nonzero integral determinant, $|\det C|\ge1$. Define
\[
\mu(L)=-\frac{\log\det\operatorname{Gram}(L)}
 {\operatorname{rank}L}.
\]
Taking logarithms in (2) gives the exact rank-defect bound
\[
\mu(B)\ge
\frac r{r+d}\bigl(\mu(A)-2P\bigr)
-\frac{2d}{r+d}\Lambda.
\tag{3}
\]

The native declarations construct the completion, prove (2), and derive (3). They expose precisely what a useful arithmetic instance must supply.

### Multiple maps have a real rank cost

For $q$ jointly injective maps $A\to B$, bundle them into the Hilbert direct sum $B^q$. The required bound is the **collective** one
\[
\sum_{h=1}^{q}\|\phi_h(x)\|^2\le e^{2P}\|x\|^2.
\]
The target rank is $q\operatorname{rank}B$. Embed each actual short generator of $B$ in a single coordinate of $B^q$; its norm is unchanged. Thus there is no artificial square-root-of-$q$ charge on the generator side. This does not entitle us to replace $q$ by the theta multiplicity $m$.

### Number-field scope is a substantive boundary

The current native theorem is a Euclidean \(\mathbb Z\)-lattice theorem. Alpöge's original descent is over finitely generated \(\mathcal O_K\)-submodules with norms at every embedding. An \(\mathcal O_K\)-integral set spanning over $K$ does not automatically furnish a \(\mathbb Z\)-spanning set with the same bounds.

A faithful bridge needs either an all-embedding determinant/product-formula proof over the original modules, or explicit restriction-of-scalars accounting for integral bases, ideals and covolumes. For a common matrix over \(\mathcal O_K\), the useful global determinant credit is the nonzero integer norm of its determinant. An individual complex embedding of that determinant need not have absolute value at least one. The treatment of nonfree projective modules must also be supplied. No field or discriminant cost has been divided away here.

## 2. What the original constructors actually pay

The detailed pinned declaration ledger is in [the constructor note](ALPOGE_NATIVE_DESCENT_CONSTRUCTORS_20261122.md). These external proof bodies were source-inspected; they are not imported or represented as independently kernel-verified by this PR.

The original finite descent is `GlobalTheory.DescentFamily.descent` in [HtMapLeOfPoints.lean](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HtMapLeOfPoints.lean). It assumes actual integral maps, joint injectivity, the collective squared-norm bound, actual small spanning generators, and
\[
q\operatorname{rk}_K B\le(1+\varepsilon_{\rm rk})\operatorname{rk}_K A.
\]
It concludes
\[
t\le\operatorname{slope}_{\rm sq}(A)-2P
\quad\Longrightarrow\quad
\operatorname{slope}_{\rm sq}(B)
\ge t-\varepsilon_{\rm rk}(|t|+2\Lambda).
\]

Its actual map supplier is `mapsCore`: choose one integral cusp section $u$, use its translated multiplication maps and coordinate projections of `cuspPh), and take $q=|S|$. The same $u$ must have a level determinant that is a non-zero-divisor. The collective norm bill is
\[
|S|^3 B^2\le e^{2b},
\]
where $B$ bounds multiplication by every translated section. The construction of $u$, its level determinant and its norm is an essential input, not a coordinate change.

The small generators have a different supplier. Unnormalized twisted traces of actual short integral section generators produce integral character-eigenvectors. The trace costs $|S|$, giving
\[
\log|S|+B_{\rm gen}\le PP\kappa.
\]
Dividing the trace by $|S|$ before proving integrality would erase an actual cost.

The near-rank estimate comes from valuations, jet orders, component and cover degrees, and share bounds. The actual descent invocation uses
\[
P=b,\qquad\Lambda=PP\kappa,\qquad
\varepsilon_{\rm rk}=\frac b{PP\kappa}.
\]
Consequently $2\varepsilon_{\rm rk}\Lambda=2b$. This is the quantitative mechanism: a very small rank defect offsets a very large generator budget. The remaining $\varepsilon_{\rm rk}|t|$ term is handled in the original lower-slope and covolume estimates; it is not zero.

The native CR/coefficient-basis certificates already transport exact arithmetic and metrics. They do not yet supply the same short cusp section, level determinant, short spanning set and geometric rank comparison. Constructing those compatible data remains necessary.

## 3. The complete signed width payment

See [AlpogeNativeSignedWidthPayment.lean](../RHLean/Analysis/AlpogeNativeSignedWidthPayment.lean), [AlpogeNativeWidthRecombination.lean](../RHLean/Analysis/AlpogeNativeWidthRecombination.lean), and [AlpogeNativeAffineFamilyPayment.lean](../RHLean/Analysis/AlpogeNativeAffineFamilyPayment.lean).

Let $D_a(w)=\operatorname{Re}(\mathrm{ASK}-\mathrm{MAIN})$, with the original inertia, Frobenius data and cutoff. Fourier inversion makes the physical coefficient at each prime power nonnegative. Every von Mangoldt term remains present. Thus ASK is convex in the width profile, even though its character expansion is signed.

For $c=(w_0+w_1)/2$, exact recombination gives
\[
D_a(c)=\frac{D_a(w_0)+D_a(w_1)}2+J_{\log}-J_{\rm ASK},
\qquad J_{\rm ASK}\ge0.
\tag{4}
\]
If $w_0,w_1\ge\beta>0$ and $|w_0-w_1|\le d$ pointwise, then
\[
0\le J_{\log}\le\frac{a d^2}{8\beta^2}.
\tag{5}
\]
The factor counting physical sites cancels against their actual mean in MAIN. No host-cardinality multiplier is charged for the ASK collar. An oriented tangent identity also retains the complete centered linear response, the positive logarithmic remainder, and the favorable negative collar.

For the original affine row form
\[
w_j(\rho)=v(\rho)+(j+\tfrac12)h_0,
\]
pair (j) with (m-1-j). Their pointwise midpoint is $v(\rho)+mh_0/2$, and their complete linear responses cancel. This pairing works for odd $m$ as well. The reference still retains every sector and torsion-dependent base; it is not a constant-width profile or a presumed realized lattice.

Summing over the actual rows and a finite set of frames, allowing variable heights $a_t\le A$, then dividing by $Q=Tmb\Delta/2$, gives the explicit normalized price
\[
\frac{A(mh_0)^2}{4b\beta^2\Delta}.
\tag{6}
\]
The equality between this family normalizer and the character-derived divisor is stated explicitly in the native normalization module.

With the actual smallest thin base \(\beta=b/(nX')\), (6) is exactly
\[
\frac{A(mh_0)^2 n^2(X')^2}{4b^3\Delta}.
\]
For $A\le2xb$, it is bounded by
\[
\frac{x(mh_0)^2 n^2(X')^2}{2b^2\Delta}.
\tag{7}
\]
The $n^2$ in (7) is retained. The fact that the ASK comparison itself has no host-size factor does not erase the host dependence of the smallest width.

The original `HCVal` and its explicit constructor have this affine form at every site. The physical widths use the `e_j` rows, with the correct shifted index in `wj`; a different shifted auxiliary width must not be substituted. The same-instance `RankVal`, `HostVal`, `HCVal` and geometric realization still need native construction.

Finally, simultaneous positive scaling of every width and the height by \(\alpha\) scales the **complete** native source by \(\alpha\), preserves every ratio (a/w) and the cutoff, and preserves source divided by $Q$ when $Q$ scales too. This is an exact analytic normalization. It does not assert integrality or realization of a rescaled lattice.

### Construct the complete physical cutoff

The midpoint comparison uses the same finite cutoff on both sides. To identify it with the full native De, every actual ratio must satisfy $a_t/w(\rho)\le N$. With $a_t\le A$ and $w(\rho)\ge\beta>0$, choose the actual integer

\[
N=\left\lceil A/\beta\right\rceil.
\]

The native finite-family lemma proves this cutoff for every original affine row and for its midpoint; the source identity is then proved at that constructed cutoff. For $\beta=b/(nX')$ and $A\asymp xb$, this cutoff is of order $xnX'$. It is different from the critical thick-response scale $x=R_V^2-1$. Replacing the full physical cutoff by $x$ would delete genuine thin-sector prime powers.

## 4. Derive the character divisor and pay the thick movement

See [AlpogeNativeSubgroupProjection.lean](../RHLean/Analysis/AlpogeNativeSubgroupProjection.lean), [AlpogeNativeThickFreezing.lean](../RHLean/Analysis/AlpogeNativeThickFreezing.lean), and [AlpogeNativeCompleteSourcePayment.lean](../RHLean/Analysis/AlpogeNativeCompleteSourcePayment.lean).

Average over the actual subgroup $A_0\subseteq H$. Character orthogonality kills exactly the characters nontrivial on this subgroup. The native physical colour normalization has $|\Phi|=2|H|$; summing the actual thick set produces $b\Delta/2$. The actual $T$ heights and $m$ rows then produce
\[
Q=Tmb\Delta/2.
\]
There is no inserted multiplicity in $G_z$, no unidentified proportionality constant, and no unproved normalization division.

The full physical source is split into the chosen thick colours and their literal finite complement. Freezing only the thick widths leaves the thin return **exactly unchanged**. The Fourier-inverted all-prime-power kernel has total colour mass at most two. The positive-part hinge is Lipschitz in width, and MAIN has the favorable sign for this lower-width comparison. Hence the total frozen-width bill before normalization is at most
\[
2hm\sum_{t\in TT}\psi(\lfloor a_t/b\rfloor).
\]
The native elementary bound
\(\psi(N)\le$\log4+2$N\) pays this after dividing by $Q$:
\[
\frac{2hm\sum_t\psi(\lfloor a_t/b\rfloor)}{Q}
\le\frac{4h(\log4+2)X}{b\Delta}.
\]
Combining the exact projection, the excluded-character charge and this genuine arithmetic inequality gives (1).

This is stronger than merely defining a width error and assuming it small. It still leaves the actual geometric source minus the signed thin return to be controlled.

## 5. Normalize the original complete geometric error bracket

See [AlpogeNativeCostNormalization.lean](../RHLean/Analysis/AlpogeNativeCostNormalization.lean).

Set $e=x^\varepsilon$, $h_2=|T2|\$, and $\Delta=h_2/n$. The original three-term bracket, after writing $x^{-\varepsilon}=1/e$, is
\[
E=T a_E\left(1+\frac{m^2}{k}\right)
 +m\left(2nmb e+
 \frac{h_2 k b e}{n(n/e)}\right).
\]
Exact division by the earned $Q$ yields
\[
\frac EQ=
\frac{2a_E}{mb\Delta}\left(1+\frac{m^2}{k}\right)
+\frac{4nme}{T\Delta}
+\frac{2ke^2}{nT}.
\tag{8}
\]
The original additive transport cost also has the exact normalization
\[
\frac{2Tmb/x}{Q}=\frac4{\Delta x}.
\]
Equation (8) explains exactly where multiplication by $m$ helps and where it costs. A factor $x^{C\varepsilon}$ multiplying the original bracket multiplies every term in (8); it cannot be discarded.

The native algebra proves these identities. It does **not** assert the geometric theorem $Z\le x^{C\varepsilon}E\$. The original `ch_top` obtains that from `IdentU`, eleven `SizeData₂` components, the strong `ErrWindows`, `BNBoundsU` and the large-parameter condition. Those are the next compatible constructor and estimate obligations.

## 6. Verification and the next genuine construction

The root manifest includes every new native proof module. [The guarded axiom audit](ALPOGE_NATIVE_DESCENT_PAYMENT_AUDIT_20261122.lean) compiles their important roots and accepts only `propext`, `Classical.choice` and `Quot.sound`. Ordinary finite geometric hypotheses remain visible in the theorem signatures; an axiom audit does not discharge them.

The proof PR does not import an external terminal RH theorem, add an axiom, redefine the source to satisfy a bound, or claim scalar endpoint transfer from the character signal.

The [width source and cost note](ALPOGE_NATIVE_WIDTH_COST_20261122.md) identifies the actual affine-row and parameter constructors. The separate native exponential-decay theorem proves that the resulting explicit polynomial times stretched-exponential scalar ledger is eventually below every fixed inverse power. Its application still needs the stated bounds on the same realized family.

The [thin-source supplier audit](ALPOGE_NATIVE_THIN_SUPPLIER_20261122.md) traces the actual positive analytic supplier, including its conductor dependence, tail-integral identity and real-character zero exclusion. It also records a necessary source-compatibility check: native responses branch on the additive host character, whereas the analytic response branches on whether the induced primitive Dirichlet character is principal. A faithful same-host map, for example a surjective modular-unit map, must justify this identification. The existing exact expansion for arbitrary maps does not assert it.

The next construction must supply, on one native realized family:

1. the original integral section lattices with their all-place metrics and arithmetic covolumes;
2. the actual short section whose translated multiplication maps are integral and jointly injective;
3. its collective norm budget, the short spanning generator family, and the geometric near-rank estimate;
4. the identification of its geometric cost with the full native ASK−MAIN and the strong weighted error window;
5. the complete signed thin/character estimate and the final character-window or scalar endpoint transfer.

The original code contains concrete suppliers for these items. The present attack has extracted their finite mechanism and removed specific width/normalization losses, but has not reconstructed those source-specific geometric suppliers in RH_Lean. This is the exact remaining boundary of the complete-source claim.

