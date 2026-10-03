# Floor-Li discrete mismatch / NNS.meboot note

The finite experiment under `numerics/floor_li_discrete_meboot/` tests the integer coordinate now formalized in `VF_MID_FLOOR_LI_DISCRETE_BACKLOG.lean`.

Define
\[
Q_n=\lfloor Li_2(n)\rfloor,\qquad
\xi_n=1_{\mathbb P}(n)-(Q_n-Q_{n-1}).
\]
For the tested range \(n>56^2\), \(\xi_n\in\{-1,0,1\}\), and the square-block identity was checked exactly:
\[
P_R-(Q_{(R+1)^2}-Q_{R^2})
 =\sum_{R^2<n\le(R+1)^2}\xi_n.
\]

The exhaustive primitive run through \(3162^2\) found lattice lag-1 correlation `-0.0719121087` and mismatch-event lag-1 correlation `-0.3667695403`.  The exact square-block floor-Li errors have standardized lag-1 `-0.1408353596`.

A full 4,611-path NNS.meboot stress suite on those exact square-block sums reaches realized lag-1 `0.9714128` at the strongest persistence stress while the maximum finite
\[
|\pi(R^2)-\lfloor Li_2(R^2)\rfloor|/(R\log R)
\]
stress ratio remains `0.4803811`; the integerized companion remains `0.4795643`.

These numerics do not establish an asymptotic bound.  They do sharpen the proof search: a deterministic theorem may tolerate very large positive dependence, while the actual primitive carrier exhibits local anti-persistence.  A particularly concrete next lemma is to formalize that same-sign adjacent primitive mismatches are impossible beyond a fixed small cutoff: consecutive actual-prime +1 events are excluded by parity, and consecutive floor-Li -1 events are excluded once
\[
Li_2(n+1)-Li_2(n-1)<1.
\]
That local statement is not sufficient for RH by itself, but it is a genuine deterministic coherence restriction on the exact integer backlog carrier.
