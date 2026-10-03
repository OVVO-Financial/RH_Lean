# Floor-Li transport mining and cancellation note

Date: 2026-10-03

This note records the finite diagnostics that motivated
\`research/VF_MID_FLOOR_LI_TRANSPORT_CANCELLATION.lean\`.

The theorem file and this note have deliberately different scopes:

- **Lean theorem:** exact identities connecting the floor-Li correction to the
  backlog derivative, primitive ternary mismatch stream, chronological owner
  census, Mobius/Abel carrier, quadratic perturbation boundary energy, and a
  global signed transport chamber formula.
- **Finite computation only:** the short relocation lifetimes, correlations,
  feedback regressions, and numerical percentages below.

No finite statistic below is used as an asymptotic theorem.

## 1. Control coordinate

Let

\[
Q(n)=\lfloor Li_2(n)\rfloor,\qquad
\xi_n=1_{\mathbb P}(n)-(Q(n)-Q(n-1)).
\]

Above the small cutoff already formalized in
\`VF_MID_FLOOR_LI_SIGNED_POPULATION_BALANCE.lean\`,

\[
\xi_n\in\{-1,0,1\}.
\]

At square endpoints define

\[
E_R=\pi(R^2)-Q(R^2)
\]

and for one square block

\[
P_R=\pi((R+1)^2)-\pi(R^2),\qquad
F_R=Q((R+1)^2)-Q(R^2),
\]

\[
\delta_R=P_R-F_R.
\]

The new Lean file names this correction
\`vfMidFloorLiActualBlockCorrection R\` and proves exactly

\[
\delta_R=E_{R+1}-E_R
       =\sum_{R^2<n\le (R+1)^2}\xi_n.
\]

It also proves

\[
\delta_R=-\,\texttt{vfMidFloorLiBlockPrimeDefect}(R),
\]

so on the existing parity/owner carrier it is exactly

\[
\delta_R
=
\text{floor-Li composite reference}
-
\text{chronological owner census}.
\]

Finally, by specializing the previously compiled floor-Li/Mobius/Abel theorem,

\[
\left\|
\delta_R-
\operatorname{MoebiusAbelCarrier}(R^2,(R+1)^2)
\right\|<1.
\]

The sub-one error is only endpoint floor rounding.

## 2. Primitive event relocation through \(10^8\)

The new miner evaluates every integer site from

\[
56^2=3136
\quad\text{through}\quad
10^8.
\]

Thirty Li values near an integer were re-evaluated at high precision before
flooring.

Observed backlog:

- start: \(-13\)
- final: \(-753\)
- primitive minimum: \(-895\)
- primitive maximum: \(-9\)

Primitive event census:

| event type | count |
|---|---:|
| floor-Li-only jump, \(\xi=-1\) | 5,428,268 |
| actual-prime-only jump, \(\xi=+1\) | 5,427,528 |
| coincident prime and floor-Li jump | 333,482 |

Only

\[
0.0578860304
\]

of actual-prime events coincide with a floor-Li jump.

Equivalently, the fraction of the union of event sites that is mismatched is

\[
0.9701962897.
\]

Thus the usefulness of floor Li is **not** explained by pointwise event
alignment. Roughly 97% of the union of event locations is relocated.

## 3. Monotone/FIFO relocation geometry

Because the observed primitive backlog remains strictly negative throughout
the finite run, the floor-Li-leading events can be monotonically paired with
later actual-prime-only events after consuming the initial deficit of 13.

Finite pairing statistics through \(10^8\):

- matched relocations: **5,427,515**
- unmatched floor-Li-leading events at the terminal endpoint: **753**
- median integer displacement: **8,781**
- mean displacement: **8,608.1194**
- 99th percentile displacement: **15,852**
- maximum displacement: **17,325**

Using the miner's square-root-bin coordinate
\(\lfloor\sqrt n\rfloor\):

| bin displacement | pairs |
|---:|---:|
| 0 | 1,833,221 |
| 1 | 3,594,100 |
| 2 | 194 |

Hence

\[
99.99642562\%
\]

of matched relocations close in the same or immediately following
square-root bin, and no observed relocation spans more than two such bins.

**Convention warning.** The fast \(10^8\) script bins events by
\(\lfloor\sqrt n\rfloor\). Exact half-open square blocks
\((R^2,(R+1)^2]\) differ only at square endpoints, but the displayed
99.9964% statistic should be cited as a square-root-bin result unless the
endpoint convention is explicitly normalized.

The empirical maximum bin lifetime of 2 is a finite observation, not a theorem.

## 4. Global transport chamber formula

The formalization packages the closed-form interpretation suggested by the
mining.

A signed relocation with birth \(a\), death \(b\), and sign \(\sigma\) is

\[
I_{\sigma,a,b}(n)
=
\sigma\,1_{a\le n}
-
\sigma\,1_{b\le n}.
\]

For \(a\le b\),

\[
I_{\sigma,a,b}(n)
=
\sigma\,1_{a\le n<b}.
\]

For a finite family of relocations,

\[
H(n)=\sum_j \sigma_j\,1_{a_j\le n<b_j}.
\]

Lean proves that its first difference is exactly the signed endpoint stream:

\[
H(q)-H(q-1)
=
\sum_j
\left[
\sigma_j1_{q=a_j}
-
\sigma_j1_{q=b_j}
\right].
\]

This is the hydrotope-style global activation formula: changes in spacing
alter interval lengths, not the algebraic cancellation law.

The repository does **not** yet assert that the actual floor-Li mismatch has a
uniform asymptotic short-lifetime transport certificate. The numerical FIFO
pairing supplies such a certificate only on the tested finite range.

## 5. Quadratic cancellation is frequency-blind after summation

For a control defect with consecutive values \(D,D'\), perturb it by arbitrary
endpoint displacements \(e,e'\).

The new theorem
\`quadraticPerturbationStep_eq_boundaryIncrement\` proves in any commutative
ring:

\[
\begin{aligned}
&\Big((D'+e')-(D+e)\Big)^2
+2(D+e)\Big((D'+e')-(D+e)\Big)\\
&\qquad-
\left((D'-D)^2+2D(D'-D)\right)\\
&=
\left(2D'e'+e'^2\right)
-
\left(2De+e^2\right).
\end{aligned}
\]

Therefore arbitrary local changes of frequency, phase, spacing, sign, or
correlation contribute only a **boundary-energy difference after summation**.
This is the exact algebra behind the earlier perturbation stress tests and is
why local event correlation is not the correct invariant.

## 6. Floor-Li backlog energy through \(R=10,000\)

For \(56\le R<10,000\), with

\[
E_{R+1}=E_R+\delta_R,
\]

the exact energy step is

\[
E_{R+1}^2-E_R^2
=
\delta_R^2+2E_R\delta_R.
\]

Finite totals:

- \(\sum\delta_R^2=2,181,482\)
- \(\sum 2E_R\delta_R=-1,614,642\)
- net endpoint energy change \(=566,840\)
- signed cross term cancels **74.0158%** of the positive diagonal total
- absolute net step / gross absolute step \(=0.00600716\)
- lag-1 correlation of \(\delta_R\): **-0.0991422**
- final \(|E_R|/(R\log R)\) at \(R=10,000\): **0.00817559**

These statistics are diagnostic only. The energy identity itself is now
formalized as \`vfMidPrimeFloorLiBacklog_energy_step\`.

## 7. Primitive event energy through \(3162^2\)

The previously exact primitive stream through \(9,998,244\) gives:

- \(\xi=-1\): 619,749
- \(\xi=+1\): 619,431
- mismatch-event lag-1 sign correlation: **-0.36676954**
- maximum event-time same-sign run: 11 for \(-1\), 7 for \(+1\)

Conditioning the primitive energy step on event sign:

| sign | total energy step |
|---:|---:|
| \(-1\) | +214,198,583 |
| \(+1\) | -214,089,191 |

Net:

\[
109,392.
\]

The two enormous sign-conditioned totals therefore nearly cancel even though
the event stream is not strict alternation.

## 8. State-feedback diagnostic

The raw square-block correction has a weak but persistent restoring
orientation.

For \(R\ge1000\), a regression of \(\delta_R\) on the current backlog \(E_R\)
and scale \(R\) gives approximately

\[
\delta_R
=
-1.08394
-0.0239493\,E_R
-0.00152843\,R
+\text{residual},
\]

with \(R^2\approx0.01195\).

The explanatory power is deliberately small; this is a noisy local effect,
not a deterministic law. The sign, however, survives fixed-scale windows.
Comparing the deepest and shallowest backlog quartiles inside consecutive
1000-block windows:

| R window | deep mean \(\delta_R\) | shallow mean \(\delta_R\) |
|---|---:|---:|
| 1000-2000 | +1.429 | -1.743 |
| 2000-3000 | +2.059 | -1.704 |
| 3000-4000 | +1.732 | -2.672 |
| 4000-5000 | +3.563 | -1.620 |
| 5000-6000 | +0.522 | -2.221 |
| 6000-7000 | +2.628 | -1.383 |
| 7000-8000 | +3.108 | -3.231 |
| 8000-9000 | +0.940 | -2.610 |
| 9000-10000 | +2.996 | -1.750 |

Every tested window has the same restoring orientation.

Again, this is numerical evidence only.

## 9. Proof interpretation

The finite experiment suggests a sharper proof search than matching actual
prime locations to Li locations.

The exact theorem-grade chain is now:

\[
\boxed{
\text{actual-floorLi block correction}
\leftrightarrow
\text{primitive ternary mismatch}
\leftrightarrow
\text{owner-census correction}
\leftrightarrow
\text{Mobius/Abel carrier}
}
\]

with less than one count of deterministic endpoint rounding in the last
coordinate change.

The transport interpretation says that if the primitive mismatch can be
globally paired into signed birth/death intervals, the cumulative backlog is
an active-interval count rather than an uncontrolled sum of local errors.
The finite data show extremely short square-root-bin lifetimes despite almost
complete event relocation.

A sufficient asymptotic route would be to prove a deterministic lifetime or
active-population envelope strong enough that the number of intervals crossing
\(R^2\) is \(O(R\log R)\). Combined with the already-proved root-scale
floor-Li/VF bridge, that would give the direct square-endpoint von-Koch target.

The finite observation "maximum lifetime 2 through \(10^8\)" is far stronger
than needed heuristically, but it is **not** assumed by the formal proof.

## 10. Reproduction

The new directory \`numerics/floor_li_transport/\` contains the \(10^8\)
transport/block miner and a compact committed result summary.

The older exhaustive primitive and NNS stress suite remains in
\`numerics/floor_li_discrete_meboot/\`.
