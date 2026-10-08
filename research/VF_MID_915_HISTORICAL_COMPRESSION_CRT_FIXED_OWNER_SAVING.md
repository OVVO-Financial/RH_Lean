# #915: exact compression restoration and fixed-wheel historical cancellation

**October 8, 2026 — Research audit.** These are mathematical advances on the original physical prime/VF source. They do **not** establish the outstanding first-bad signed payment or RH.

## 1. Exact NNS historical compression restoration

Let the genuine signed historical carrier consist of the earlier anchor \(-D_A\) and the actual original VF odd-seat charges \(z_r(n)=w_r-\mathbf 1_{\mathbb P}(n)\) in blocks \(A\le r<R\). Let \(U_H,L_H\) be its zero-target upper and lower partial moments. The historical signed telescope gives

\[
U_H-L_H=-D_R,\qquad
U_H+L_H=|D_A|+
  \sum_{A\le r<R}\sum_{n\in O_r}|z_r(n)|.
\]

Write \(C_R=\sum_{n\in O_R}|z_R(n)|\) for the *unchanged* current-block original absolute mass. There is no independent historical parent after compression.

**Exact restoration identity**:

\[
\boxed{
 (U_H+L_H+C_R)^2-(|D_R|+C_R)^2
 =4U_HL_H+2C_R(U_H+L_H-|U_H-L_H|).
}
\tag{1}
\]

The first term is exactly the historical opposite-sign quadratic partial-moment interaction; the second is the precise cross-current absolute-capacity adjustment. They are *mandatory restorations*, not new negative energy that can be claimed for free.

Equivalently, the original signed normalized Co/Div excess equals the expanded signed excess **plus the full restoration (1)**. The huge experimental decompression cost therefore can be tracked exactly with the original NNS masses.

**Lean:** research/VF_MID_915_EXACT_HISTORICAL_NNS_COMPRESSION.lean imports the already-compiled historical endpoint identity and original vfMidFirstBadZeroTargetTotalMass, proves upper-minus-lower equals \(-D_R\), upper-plus-lower equals the *actual* historical \(L^1\) mass, and then (1). A proof of the positive restoration formula is *not* itself the RH-strength signed payment.

## 2. A new universal square-block cancellation theorem for any fixed wheel

Let \(W\ge2\) be **any** positive integer, not necessarily a primorial. Define

\[
\chi_W(n)=\mathbf1_{\gcd(n,W)=1},\qquad
N_W(r)=\sum_{r^2<n<(r+1)^2}\chi_W(n),\qquad
\epsilon_W(r)=N_W(r)-\frac{2\varphi(W)}W r.
\]

### Theorem A: exact square-index periodicity

\[
\boxed{\epsilon_W(r+W)=\epsilon_W(r).}
\]

**Proof.** The open-square interval after replacing \(r\) by \(r+W\) begins in the same wheel residue, and is precisely \(2W\) integers longer. These are two extra full periods, each containing \(\varphi(W)\) coprime integers. Hence \(N_W(r+W)=N_W(r)+2\varphi(W)\); subtract the deterministic change of \(2\varphi(W)\). QED.

### Theorem B: exact period cancellation

\[
\boxed{\sum_{r=0}^{W-1}\epsilon_W(r)=0.}
\]

**Proof.** The union of the open square blocks \(0\le r<W\) is the interval \(0<n<W^2\) with the \(W-1\) interior squares \(k^2\), \(1\le k<W\), removed. Exactly \(W\varphi(W)\) integers in \(0\le n<W^2\) are coprime to \(W\), and exactly \(\varphi(W)\) of those omitted squares are coprime, because \(\gcd(k^2,W)=1\) if and only if \(\gcd(k,W)=1\). Thus \(\sum_{r<W}N_W(r)=(W-1)\varphi(W)\). The smooth term sums to \((2\varphi(W)/W)\sum_{r<W}r=(W-1)\varphi(W)\). Difference zero. QED.

### Theorem C: all-long-run uniform bound

Put \(T_W(k)=\sum_{0\le r<k}\epsilon_W(r)\) for \(0\le k\le W\). From A+B, for **arbitrary** square endpoints \(0\le A\le B\),

\[
\boxed{
\sum_{r=A}^{B-1}\epsilon_W(r)
=T_W(B\bmod W)-T_W(A\bmod W),
}
\tag{2}
\]

and hence

\[
\boxed{
\left|\sum_{r=A}^{B-1}\epsilon_W(r)\right|
\le \max_{0\le k\le W}T_W(k)
    -\min_{0\le k\le W}T_W(k).
}
\tag{3}
\]

No randomness, PNT assumption, probabilistic mixing, or prime equidistribution is involved. **Small fixed-wheel owners cannot create indefinite cumulative signed square-block drift.** The proof specifically uses the omitted-square endpoints and the fact that coprimality of a square is equivalent to coprimality of its square root.

A crude but uniform bound on each \(|\epsilon_W(r)|\) is \(2\varphi(W)\), since a finite interval differs from its full-period density only by at most two incomplete periods. Hence the right side of (3) is at most \(2W\varphi(W)\le2W^2\). Even a **growing** primorial wheel satisfying \(W\le\sqrt R\) therefore has \(O(R)\) long-run error, below the \(R\log R\) target. All primes beyond that wheel remain uncontrolled.

### Exact sharp finite certificate for the 2×3×5×7×11×13×17 wheel

For \(W=510510\),

\[
\varphi(W)=92160,\quad
\frac{2\varphi(W)}W=\frac{6144}{17017}.
\]

The executable exact-integer/rational script independently computes all \(510510\) square phases, certifies their zero sum, checks all \(p\)-centered CRT owner reconstructions for \(p=3,5,7,11,13,17\), and finds

\[
\boxed{
\max T_W-\min T_W=\frac{46460}{2431}
=19.1114767585\ldots
}
\tag{4}
\]

Thus the all-run finite-certificate consequence is

\[
\boxed{
\left|\sum_{r=A}^{B-1}
 \left[
 N_{510510}(r)-\frac{6144}{17017}\,r
 \right]\right|
\le\frac{46460}{2431}\qquad(0\le A\le B).
}
\tag{5}
\]

The less sharp (owner-by-owner absolute) bound is \(6352/221\approx28.742\). The strict improvement in (4) proves that **real cross-owner cancellation survives** when one first reassembles the complete fixed wheel, rather than bounding each owner separately.

**Status:** (2)-(3) follow from the unconditional elementary proofs above. Constant (4) is checked exhaustively via the exact-rational GitHub Actions regression scripts/vf_mid_915_fixed_owner_crt_history_regression.py; the finite certificate is **not yet itself a kernel-checked Lean theorem**. Do not conflate an exact executable finite certificate with a Lean declaration.

Exact representative signed square-run wheel deviations:

| \([A,B)\) | Exact deviation |
|---|---:|
| [10,19) | \(3665/2431\) |
| [29,57) | \(-379/143\) |
| [159,318) | \(160/143\) |
| [514,1028) | \(26519/17017\) |
| [3001,6001) | \(-71726/17017\) |
| [50001,100001) | \(38502/17017\) |

## 3. Direct quantitative transfer to original VF actual primes

For \(r\ge17\), every prime in the actual open square block survives this fixed wheel. Let

\[
T_{>17}(r)=N_{510510}(r)-P_r
\]

be the **actual** number of surviving composites whose least prime factor is \(>17\). This is a real integer census, not an independence model.

The exact block tracking forcing \(F_r=V_r-P_r\) satisfies

\[
\boxed{
\sum_{r=A}^{B-1} F_r =
  \sum_{r=A}^{B-1}\left(V_r-\frac{6144}{17017}r\right)
  +\sum_{r=A}^{B-1}T_{>17}(r)
  -\sum_{r=A}^{B-1}\epsilon_{510510}(r).
}
\tag{6}
\]

Consequently, for **any** \(17\le A<B\),

\[
\boxed{
\left|\sum_{r=A}^{B-1}F_r-
\left\{\sum_{r=A}^{B-1}
  \left(V_r-\frac{6144}{17017}r\right)
  +\sum_{r=A}^{B-1}T_{>17}(r)
\right\}\right|
\le19.112.
}
\tag{7}
\]

Equation (7) removes the entire long-run signed uncertainty of ALL least-prime owners \(2,3,5,7,11,13,17\) at a fixed \(O(1)\) cost. This is a genuine unconditional quantitative bound, not a reformulation of the full prime error. **It does not bound the moving large-owner remainder \(T_{>17}\).**

For #915's canonical \(A=\lfloor R/2\rfloor+1\), (7) applies when \(R\ge32\). It isolates where the first-bad arithmetic expense **must** live: in the actual correlated higher-owner remainder, together with the original signed historical/current quadratic interactions.

## 4. Centered triangular owner covariance is not a global sign theorem

The research module VF_MID_915_CENTERED_OWNER_TRIANGULAR.lean proves a genuine pointwise arithmetic relation on the same physical n:

\[
\xi_p(n)\xi_q(n)=-\frac1p\xi_q(n)
\quad (p<q).
\]

This is a nontrivial algebraic reduction of **same-site/different-owner** correlations. It is NOT a sign estimate on **different-site** products \(\xi_p(n)\xi_q(m)\), \(n\ne m\), which are the actual long-range quadratic covariance at the heart of RH.

The new fixed-wheel theorem controls total historic contributions of the first seven owners independently of run length; the remaining moving-owner signed quadratic response is not yet controlled. No one should infer from triangularization that the entire original first-owner Co/Div excess is nonpositive.

## 5. Updated single mathematical requirement

With historical compression restored exactly by (1), and small-owner long-run discrepancy bounded by (7), the open step remains a **first-bad-specific signed covariance bound on the actual moving high-owner / survivor-restricted historical-current carrier** in its original compressed norm. Neither PNT's main term nor the completed Möbius-prefix/cross-owner pair identities alone proves that the remaining signed error is RH-scale.

The target is unchanged:

\[
\mathrm{ActiveGlobalResidualExcess}(R)
\le \mathrm{ThreeBoundaryTransportedExcess}(R)
  +4\,\mathrm{ThreeBoundaryAbsMass}(R)
\]

under the genuine first-bad hypothesis, implying the original anchored hbalance statement. The finite-wheel saving and restoration identity are new proved/verified ingredients, not a completed solution.
