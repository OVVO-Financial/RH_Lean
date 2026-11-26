# Quantitative discrepancy ledger for #1201

The three transfer errors below have a uniform bound with exponent coefficient 1. The independent bound derived below for the comparison source is weaker than the critical estimate. Existence of a measured geometric frame with the required signed gain at every anchor on cofinal windows remains open.

Hosted Lean verified the assembled inequality, its normalized price and the independent physical mass bound at commit `393cb5c`. The same job verified the refinement that freezes only the thick widths. [Proof and axiom audit](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45780078438/job/139773341050).

## The two sources

Fix $0<\varepsilon<1/52$ and a window exponent $A\ge1$. Take $e(x)$ and the pair $(q,d)$ for the window $[Y,Y^A]$ from `nativeConstructedDyadicGzPayment`. The pair stays fixed throughout that window. On its actual reciprocity host $H$, use a nonempty physical top set $TT$, nonempty thick set $T_2$, $m>0$, positive $b$, heights $a_t$, positive widths $w_{uj\rho}$, and the density, cutoff and width conditions of that theorem. Write

$$
\Delta=|T_2|/|H|,\qquad Q=|TT|mb\Delta/2,\qquad N=\lceil A_{\max}/\beta\rceil .
$$

Here $a_t\le A_{\max}$ and $\beta$ is the original lower width bound. Require $x\ge1$ and the original height localization $x\le a_t/b\le x+1$ for every top. The upper endpoint follows from $A_{\max}/b\le x+1$. The original height window $xb\le a_t\le xb+xb/(k\sigma)$ gives both endpoints when $k\ge x$ and $\sigma\ge1$.

Let $S(v)$ be the **sum over tops and rows** of the physical $\operatorname{Re}(\mathrm{ASK}-\mathrm{MAIN})$, averaged over the whole host subgroup. Define

$$
\begin{aligned}
G_{\rm native}(x)&=\sum_{n\le x}\Lambda(n)(x/n-1)-x\log x+(1+\gamma)x,\\
\eta&=\frac{b\Delta\sqrt{x}}{2A_{\max}},\qquad
v_{uj\rho}=\exp\!\left(\eta\left\lfloor\frac{\log w_{uj\rho}}{\eta}\right\rfloor\right),\\
G_{\rm comparison}(x)&=S(v)/Q .
\end{aligned}
$$

The widths $v$ are computed from the measured widths. Both sources of physical excess, $S(w)$ and $S(v)$, use the same heights, top and thick sets, rows, inertia, Frobenius, canonical character term and cutoff $N$. A lower grid endpoint may fall below $\beta$. Keeping $N$ fixed is part of the comparison. The comparison does not require the grid endpoints to be integral sections.

## The ledger

Use $C_d=4+\log 4$ and $r=x^{1/2+\varepsilon}$. Each row gives an upper allowance in the indicated direction.

| Transfer on this frame | Allowance before dividing by $Q$ | Normalized allowance | Independent supplier |
|---|---:|---:|---|
| $G_{\rm native}(x)$ to the mean of $G_{\rm native}(a_t/b)$ | $Q C_d$ | $C_d$ | Global arithmetic Lipschitz estimate with constant $C_d$ and mean absolute height displacement at most 1 |
| Mean of $G_{\rm native}(a_t/b)$ to $S(w)/Q$ | $Qr$ | $r$ | Selected dyadic analytic payment with the complete prime-power source and its original cutoff |
| $S(w)/Q$ to $S(v)/Q$ | $\lvert TT\rvert mA_{\max}\eta$ | $2A_{\max}\eta/(b\Delta)=\sqrt{x}$ | Monotonicity of each real ASK cut and the change in the signed MAIN logarithm |

Let $E_{\rm total}$ be the sum of the three raw allowances. The resulting statement is

$$
G_{\rm native}(x)\le G_{\rm comparison}(x)+\frac{E_{\rm total}}{Q},
\qquad
\frac{E_{\rm total}}Q=C_d+r+\sqrt{x}\le (6+\log4)x^{1/2+\varepsilon}.
$$

For $x\ge (4+\log4)^2$ the coefficient can be reduced to 3. All constants in this price are independent of the frame, the selected pair, and the window. The signed width comparison uses $v\le w$ and $0\le\log w-\log v\le\eta$. The real ASK decreases as the width increases. The remaining positive change in $S(w)-S(v)$ is at most $a_t\eta$ per row. Paying that charge before division accounts for the factor $2/\Delta$.

## Independent bound for the comparison source

Write $L_N=\sum_{1\le n\le N}\Lambda(n)/n$, and let $M_{utj}=\operatorname{Re}\mathrm{MAIN}(\ell,a_t,v_{uj})$. The complete kernel on this host gives

$$
G_{\rm comparison}(x)\le
\frac{1}{Q|H|}\sum_{u\in H}\sum_{t\in TT}\sum_{j=1}^m
\bigl[2a_t L_N-M_{utj}\bigr].
$$

Indeed the real ASK weights $K_{ng}$ are nonnegative with $\sum_{g\notin\Phi}K_{ng}\le2\Lambda(n)$, including at ramified prime powers. Each cut is at most $a_t/n$. Subtracting the exact MAIN preserves its character and logarithmic terms. For $N\ge1$, the existing unconditional estimate gives $L_N\le\log N+\log4+2$. These bounds use quantities defined independently of $G_{\rm native}$. They do not give a square-root bound for $G_{\rm comparison}$.

There is a concrete way to measure what the coarse upper bound discarded. For each row set $z_n=a_t/n$, $c_{t,g}=v_{uj,\operatorname{partner}(t,g)}$, and $k_n=\sum_{g\notin\Phi}K_{ng}$. Its exact saving against the upper bound $2a_t L_N$ for ASK is

$$
\sum_{n=1}^N(2\Lambda(n)-k_n)z_n
+\sum_{n=1}^N\sum_{g\notin\Phi}K_{ng}\min(z_n,c_{t,g}).
$$

This follows from $z-(z-c)_+=\min(z,c)$. Both terms are nonnegative and can be computed from inertia, Frobenius and the measured widths. A lower estimate for these savings must be compared with the signed MAIN on the **same** frame. The identity itself gives no lower estimate of the required size.

The physical thick mask gives an independent lower bound for part of the second saving. Define
$\beta_0=\beta e^{-\eta}$, $b_0=b e^{-\eta}$ and $k^{10}_n=\sum_{h\in H}K_{n,((1,0),h)}$.
For $z_{tn}=a_t/n$ put $P_c(z)=(z-c)_+$ and
$D_{tn}=P_{\beta_0}(z_{tn})-P_{b_0}(z_{tn})\ge0$.
All grid widths are at least $\beta_0$. A selected thick partner has grid width at least $b_0$ because $v\ge e^{-\eta}w$. For fixed $t$ and $g=((1,0),h)$ there are exactly $|T_2|$ translates $u$ which select $g$. Indeed $s+u-t=h$ gives the distinct solutions $u=h+t-s$ for $s\in T_2$. The other first-bit-one colour occurs zero times in the thick mask. This calculation uses the full subgroup supplied by the selected payment.

Writing $\mathcal M=|H|^{-1}\sum_{u,t,j} M_{utj}$, the resulting stronger comparison estimate is

$$
G_{\rm comparison}(x)\le
 \frac{2}{|TT|b\Delta}\sum_{t\in TT}\sum_{n=1}^N k_n P_{\beta_0}(z_{tn})
 -\frac{2}{|TT|b}\sum_{t\in TT}\sum_{n=1}^N k^{10}_n D_{tn}
 -\frac{\mathcal M}{Q}.
$$

To verify the bound, each cut is at most $P_{\beta_0}(z_{tn})-\mathbf1_{g\text{ selected}}D_{tn}$. Multiply by the native nonnegative weight, average in $u$, and sum the $m$ rows. The factor $\Delta$ in the thick saving cancels **exactly** against the original divisor. This yields an explicit negative contribution, calculated from the actual thick translates with coefficient $2/(|TT|b)$. The cutoff and signed MAIN still contain the complete original thin and ramified data. The two positive-part functions coincide below $\beta_0$, differ by $z-\beta_0$ between the two thresholds, and differ by $b_0-\beta_0$ above $b_0$. These facts specify the contribution of each prime power. The bound for the sum over all translates of a fixed physical colour is formalized in `alpogeNativeLowerLogWidth_thick_translate_cuts_le`. The displayed aggregation multiplies those inequalities by the native weights and sums over colours, prime powers and rows. This last aggregation is a paper derivation.

### A finite signed bound using the native height, mask and kernel data

The full signed comparison also has an upper bound that preserves the interaction between the logarithm and the prime-power cuts. It can be evaluated without knowing the individual widths. Set $a_*=\sum_t a_t/|\Phi|$, $M_0=\sum_t a_t(\log a_t-1-\gamma+\operatorname{Re}\ell(\chi_C))$, with the sums over $TT$. For each positive site $\rho$, take the unique nonpositive-mask colour $g(t,\rho)$ whose partner is $\rho$. It exists because the partner is translation by $((1,1),t)$. Define the following function on $v>0$:

$$
F_\rho(v)=\sum_{t\in TT}\sum_{n=1}^N K_{n,g(t,\rho)}(a_t/n-v)_+ + a_*\log v .
$$

The same $v$ occurs for **all** tops and all prime powers at a site in a given row. Directly summing the complete signed source gives
$S(v)=|H|^{-1}\sum_{u,j}[\sum_{\rho\in\Phi} F_\rho(v_{uj\rho})-M_0]$.

Let $L(c)=\exp(\eta\lfloor\log c/\eta\rfloor)$, $X'=\exp(x^{\varepsilon/3})$ and $a_{\min}=\min_{t\in TT}a_t$. The native thick and thin conditions put the rounded widths in the respective intervals

$$
I_B=[L(b),L(b+h)],\qquad I_T=[L(\beta),L(3a_{\min}/X')].
$$

For the thin interval, apply the thin inequality to the inverse partner of $\rho$ for each top. The equivalence between a thick partner and a thick colour is `alpogeNativeFreezing_partner_mem_iff`. The logarithmic rounding function is increasing in the weak sense. Both intervals used by the physical profile are compact and strictly positive.

For either interval $I$, compute an upper bound $U_\rho(I)$ as follows. Split $I$ at the finitely many interior thresholds $a_t/n$. On each resulting open interval the active weight $k=\sum_{t,n:\ a_t/n>v}K_{n,g(t,\rho)}$ is constant and $F'_\rho(v)=a_*/v-k$. Evaluate $F_\rho$ at the two endpoints and, when $k>0$, at $v=a_*/k$ if it lies in the interval. Take the largest value, including the value at a singleton interval. This computes the continuous maximum exactly. Rounding each candidate on both sides to grid points in $I$ and retaining the endpoints also gives the exact maximum over allowable grid values, by monotonicity on either side of a stationary point. The continuous maximum already suffices.

Define $d_\rho=\Delta$ on sites with bits $(0,1)$ and $d_\rho=0$ on sites with bits $(0,0)$. The same translate count now yields an explicit signed upper bound independent of the individual widths,

$$
G_{\rm comparison}(x)\le
\frac{2}{|TT|b\Delta}
\left[\sum_{\rho\in\Phi}\left(
 d_\rho U_\rho(I_B)+(1-d_\rho)U_\rho(I_T)\right)-M_0\right].
$$

Indeed each $F_\rho(v_{uj\rho})$ is bounded on its own interval, precisely $d_\rho|H|$ translates use the thick interval, and the native divisor cancels the row count. This is a paper bound for the same comparison source in the ledger. Its inputs are the selected kernel, heights, scalar width ranges and original mask. A square-root estimate for this explicit expression would suffice. A large value of the expression alone would only rule out this uniform relaxation because maximizing independently over sites discards restrictions on jointly realizable widths. No critical bound for the maximum is established here.

## Outstanding supplier

The missing bound is $S(v)\le K_\varepsilon Qx^{1/2+C_0\varepsilon}$ on an admissible measured family for **every** anchor on arbitrarily distant complete windows $[Y,Y^{3/2}]$, with $C_0$ fixed before $\varepsilon$ and $K_\varepsilon$ independent of the window. The selected pair and host already exist; the theorem quantifies over physical profiles satisfying its explicit hypotheses. It does not establish cofinal existence of the required profiles with this signed payment. A local index contributes only through an estimate for the signed same-frame source or an independently priced one-sided comparison. The primitive evaluations and the joint finite-index, Gram and signed-slope payment are still open. No error row silently pays them.

## Lean declarations

- [nativeConstructedDyadicDiscrepancyLedger and nativeDiscrepancyPrice_le](../RHLean/Analysis/AlpogeThin/NativeExistingRecoveryPayment.lean) assemble the pointwise inequality from the selected host, price its errors, and retain the original height-window lemma.
- [nativeConstructedDyadicGzPayment](../RHLean/Analysis/AlpogeThin/NativeConstructedDyadicGzPayment.lean) supplies the analytic row. [alpogeNativeGzArithmetic_le_mean_add_move](../RHLean/Analysis/AlpogeThin/NativeScalarSupplierPayment.lean) supplies arithmetic movement.
- [alpogeNativePhysicalSubgroupTopExcess_logGrid_le and alpogeNativePhysicalSubgroupTopExcess_mass_bound](../RHLean/Analysis/AlpogeNativeThickFreezing.lean) give the physical width comparison and independent mass estimate. [nativeLambdaRecip_sub_log_abs_le](../RHLean/Analysis/NativePNTSelberg.lean) gives the numerical estimate for $L_N$.
- [Research audit roots](ALPOGE_EXISTING_RECOVERY_APPLICATION_AUDIT_20261124.lean) include the assembled ledger, normalized price and mass bound.

## Refining the width entry by freezing only the thick sites

Source: Alpöge's original `Compl3Record.lean` (lines 15–44, 217–287) and `AbsPhFSubLeOfLe.lean` (lines 52–153), pinned at [a6ac91a](https://github.com/TomasOrtega/RH/tree/a6ac91a412dcbaab31801355ec5707024a71bf65/extracted/lean/src/Formalism/SharpRestriction/Divisibility/HookProducts). This is an inequality transport, not a claim that Harish-Chandra coordinates equal native widths. The actual native signed row difference is the ASK difference plus the mean log-width difference multiplied by its height; all common character and height terms cancel. The ASK difference is nonpositive when the comparison is a lower width profile.

Use the same selected pair, host, rows, top heights, inertia/Frobenius, canonical character, cutoff and original divisor Q as above. Instead of rounding every width, let v = freezeThick(T2,u,b,w). The thin widths remain identical. The thick support has cardinal |T2|, exactly half the thick density among the 2|H| positive sites. At changed coordinates 0 <= log(w/b) <= h/b by log z <= z-1. Thus the mean log distortion is at most (Delta/2)(h/b). The existing one-sided signed-width theorem then gives

$$
S(w)/Q \le S(v)/Q + (A_{\max}/b)(h/b).
$$

The density cancels rather than being paid by an arbitrary grid tolerance. The comparison uses no manufactured geometric witnesses and no new assumptions. In the original size regime, the established numerical cost-window theorem (specialized at e=0, K=0 solely for its numerical inequality) gives (x+1)h/b <= 1/x eventually, uniformly in b,h. Since Amax/b <= x+1, the full native ledger becomes

$$
G_{\rm native}(x) \le S(v)/Q + C_d + x^{1/2+\varepsilon} + (A_{\max}/b)(h/b),
$$

with the last charge at most $1/x$ eventually. The guarded audit verified the signed row difference, thick-support count, normalized comparison and eventual price. All thin and ramified contributions remain in $S(v)$. The outstanding supplier above applies to this choice of $v$ as well.

Native declaration names: `alpogeNativeSignedWidthSource_sub_eq`, `alpogeNativeThickPositiveSites_card`, `alpogeNativeFreezeThick_logMean_le`, `alpogeNativePhysicalSubgroupTopExcess_freezeThick_upper_le`, `nativeConstructedDyadicFrozenDiscrepancyLedger`, `nativeFrozenWidthPrice_eventually`.
