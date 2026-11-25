# Quantitative discrepancy ledger for #1201

The three transfer errors below have a uniform bound with exponent coefficient 1. The independent bound derived below for the comparison source is weaker than the critical estimate. Existence of a measured geometric frame with the required signed gain at every anchor on cofinal windows remains open.

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

## Outstanding supplier

The missing bound is $S(v)\le K_\varepsilon Qx^{1/2+C_0\varepsilon}$ on an admissible measured family for **every** anchor on arbitrarily distant complete windows $[Y,Y^{3/2}]$, with $C_0$ fixed before $\varepsilon$ and $K_\varepsilon$ independent of the window. The selected pair and host already exist; the theorem quantifies over physical profiles satisfying its explicit hypotheses. It does not establish cofinal existence of the required profiles with this signed payment. A local index contributes only through an estimate for the signed same-frame source or an independently priced one-sided comparison. The primitive evaluations and the joint finite-index, Gram and signed-slope payment are still open. No error row silently pays them.

## Lean declarations

- [nativeConstructedDyadicDiscrepancyLedger and nativeDiscrepancyPrice_le](../RHLean/Analysis/AlpogeThin/NativeExistingRecoveryPayment.lean) assemble the pointwise inequality from the selected host, price its errors, and retain the original height-window lemma.
- [nativeConstructedDyadicGzPayment](../RHLean/Analysis/AlpogeThin/NativeConstructedDyadicGzPayment.lean) supplies the analytic row. [alpogeNativeGzArithmetic_le_mean_add_move](../RHLean/Analysis/AlpogeThin/NativeScalarSupplierPayment.lean) supplies arithmetic movement.
- [alpogeNativePhysicalSubgroupTopExcess_logGrid_le and alpogeNativePhysicalSubgroupTopExcess_mass_bound](../RHLean/Analysis/AlpogeNativeThickFreezing.lean) give the physical width comparison and independent mass estimate. [nativeLambdaRecip_sub_log_abs_le](../RHLean/Analysis/NativePNTSelberg.lean) gives the numerical estimate for $L_N$.
- [Research audit roots](ALPOGE_EXISTING_RECOVERY_APPLICATION_AUDIT_20261124.lean) include the assembled ledger, normalized price and mass bound.
