# Prime phases, ordinary composites, and the complete signed survivor

Date: 2026-11-17. This change supplies exact accounting and supporting proof
infrastructure. The complete signed survivor estimate, finite A/C, subpower
amplification, and RH remain open arithmetic targets.

## 1. Three different objects

The repository's death process is a height-shell process on canonical ancestry
pairs. It is not the ordinary count of composite integers. Likewise, the
survivor is a complete signed sum over prime and composite ancestry, not the
ordinary set of primes left after deleting composites.

In the original source, a pair has a prime `q` and a canonical squarefree
cofactor `c`. At stage `t`, its integer lies below

\[
X_t=(t+1)^2-1,
\]

and survival requires `2 Λ t < |q²-c²|`. The source
`RHLean/Proof/SurvivorZeroMode.lean` defines the actual signed zero mode and
proves its prime/composite partition. The already proved death-shell bound in
`RHLean/Analysis/SquareBlockDeathProcess.lean` remains supporting infrastructure;
it does not discharge the complete survivor estimate.

The new accounting module includes literal witnesses at `Λ=1`: prime 2
survives at stage 1 and does not survive at stage 2, while the canonical pair
`(c,q)=(2,3)` for composite 6 survives at stage 2. These are witnesses for the
actual source predicates, not a model with a replacement source.

## 2. Exact prime count and composite correction

`research/SURVIVOR_PRIME_COMPOSITE_ACCOUNTING_20261117.lean` defines

\[
L_{\Lambda,t}=\left\lfloor\sqrt{2\Lambda t+1}\right\rfloor.
\]

For `Λ ≥ 0`, `t ≥ 1`, and `L_{Λ,t} ≤ X_t`, it proves

\[
S_{\rm prime}(\Lambda,t)
=-\bigl(\pi(X_t)-\pi(L_{\Lambda,t})\bigr),
\]

\[
S_{\rm composite}(\Lambda,t)
=S(\Lambda,t)+\pi(X_t)-\pi(L_{\Lambda,t}).
\]

The natural subtraction is justified by the cutoff condition. The module
also proves `L_{Λ,t} ≤ t` when `t ≥ 1` and `2Λ ≤ t`, so the condition holds at
all sufficiently large stages for every fixed nonnegative `Λ`.

The complete cancellation target is therefore exactly

\[
S_{\rm composite}(\Lambda,t)
-\bigl(\pi(X_t)-\pi(L_{\Lambda,t})\bigr)=S(\Lambda,t).
\]

This is an identity, not an independently obtained estimate for its residual.

## 3. The pure-prime component cannot satisfy the survivor scale

`research/SURVIVOR_CANCELLATION_SCALE_20261117.lean` reuses the already proved
`RHLean.Analysis.nativePrimeNumberTheorem` from
`RHLean/Analysis/NativePNTTransfer.lean`. It does not postulate PNT, a
prime-phase theorem, or an RH criterion.

The proof uses a deliberately weak polynomial consequence of native PNT:
eventually `π(n⁸) ≥ n⁷`. At stages `t=n⁴`, exact accounting and the cutoff
bound give

\[
\|S_{\rm prime}(\Lambda,n^4)\|\ge n^7-n^4.
\]

Consequently, for every fixed `Λ ≥ 0`,

\[
\neg\exists C\ge0\;\forall t\ge1:\quad
\|S_{\rm prime}(\Lambda,t)\|^2\le Ct^3.
\]

This refutes componentwise application of the survivor's every-positive-loss
RH-scale energy bound: its `ε=1`, `H=1` instance would give the cubic bound.
It does not refute the complete signed survivor estimate. The composite
contribution must remain available to cancel the prime count.

The new theorem is this polynomial obstruction. The sharper asymptotic
`|S_prime(t)| ~ t²/(2 log t)` is not an output of this formalization.

## 4. All translated windows include the single-stage obstruction

For the actual complete signed survivor, the cancellation module proves

\[
\begin{aligned}
&\forall\epsilon>0\;\exists C_\epsilon\ge0\;
\forall N,H\in\mathbb N,\ 1\le H\le N:\\
&\hspace{1cm}\sum_{h<H}\|S(\Lambda,N+h)\|^2
\le C_\epsilon H N^{2+\epsilon}
\end{aligned}
\]

if and only if

\[
\forall\epsilon>0\;\exists C_\epsilon\ge0\;\forall t\ge1:
\quad\|S(\Lambda,t)\|^2\le C_\epsilon t^{2+\epsilon}.
\]

The forward direction uses `H=1`. The converse uses `N+h ≤ 2N` and changes
the constant by `2^(2+ε)`. An almost-every-stage result alone does not supply
the universal pointwise premise; exceptional stages still need control.

For `Λ>0`, a final consumer takes the unchanged complete survivor premise
directly to Mathlib's `RiemannHypothesis`, via the existing square-prefix to
Mertens-energy equivalence and `riemannHypothesis_of_mertensEnergy`. Its type
has no `ClassicalMertensRHCriterion` argument. This closes an interface in
the consumer, not the arithmetic survivor premise.

## 5. What the finite exceptional-sampling module proves

`research/PRIME_PHASE_EXCEPTIONAL_SAMPLING_20261117.lean` proves the elementary
finite packing step. If every bad root `r` has a neighborhood `U_r` contained
in a finite set `E`, the neighborhoods are pairwise disjoint, and each has
at least `m` samples, then

\[
m\,\#B\le\#E.
\]

It includes actual square neighborhoods `[R²,R²+w)` and their disjointness
under `w ≤ 2R+1`. The real-valued cardinality consumer shows that neighborhood
size at least `cY` and budget at most `C Y^(3/2+ε)` imply

\[
\#B\le(C/c)Y^{1/2+\epsilon}.
\]

All containment, persistence, disjointness, positivity, and budget inputs
remain explicit. This is a finite integer-cardinality statement. It does
not prove a Lebesgue-measure exceptional-set estimate or its conversion to
the required discrete neighborhoods. It does not prove the required prime
estimates, Brun–Titchmarsh persistence, or a zero-density theorem.

The same module proves ordinary complement identities on a finite integer
window `W` containing only integers at least 2. If `P(W)` and `C(W)` count
primes and ordinary composites, then `P(W)+C(W)=#W`, and

\[
C(W)-(\#W-P_0)=-(P(W)-P_0).
\]

Thus their absolute errors at matching precision are equal. For `I ⊆ W`,

\[
C(I)-\alpha C(W)
=(\#I-\alpha\#W)-(P(I)-\alpha P(W)).
\]

The integer-window residual is retained. These ordinary counting identities
are not substitutions for the canonical signed death/survivor source.

## 6. Literature and remaining formalization work

The following claims have different scopes and must retain different DAG
statuses.

| Statement | Status and limitation |
| --- | --- |
| Global equidistribution of `{√p}` over all primes up to a cutoff | Established classical theorem; the repository's `SquareRootPrimePhaseEquidistributionStatement` remains an explicit hypothesis in `GrowingParentPhaseUniformity.lean`. |
| Harman's `4/5+ε` global discrepancy estimate | Literature input represented by `research/VF_MID_HARMAN_FOUR_FIFTHS.lean`; not proved by this PR. Its square-scale telescope is conditional. |
| Prime asymptotics in almost all consecutive-square intervals | Established in the literature; this PR formalizes only the finite packing component, not the analytic theorem or the measure-to-discrete transfer. |
| Every square block / every survivor stage at RH scale | Not supplied by either global equidistribution or an almost-all statement. The complete signed survivor estimate remains open. |

Primary sources:

- X. Cao and W. Zhai, *On the distribution of p^α modulo one* (1999),
  [paper](https://www.numdam.org/item/JTNB_1999__11_2_407_0.pdf), including the
  historical and quantitative square-root phase results.
- G. Harman, *On the distribution of √p modulo one* (1983),
  [DOI](https://doi.org/10.1112/S0025579300010457).
- D. Bazzanella, *Primes between consecutive squares* (2000), Theorem 1,
  [author manuscript](https://iris.polito.it/bitstream/11583/1397858/2/Primes-between-squares.pdf).
- D. Bazzanella, *Prime numbers in intervals starting at a fixed power of the
  integers* (2009), Lemma 1,
  [publisher manuscript](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/C5534F28D72BA272E7494FC497339C36/S1446788709000020a.pdf/prime_numbers_in_intervals_starting_at_a_fixed_power_of_the_integers.pdf).
- A. Gafni and T. Tao, *On the number of exceptional intervals to the prime
  number theorem in short intervals* (2025),
  [preprint](https://arxiv.org/abs/2505.24017).

No edge from pooled phase equidistribution or ordinary composite counting to
the complete survivor estimate is asserted. No universal prohibition on
exact divisibility arguments is asserted.

## 7. Verification and DAG policy

The source certificate for [PR #1143](https://github.com/OVVO-Financial/RH_Lean/pull/1143)
records head `ae266e3319c502ade5fc6fa0dd95b7829612b362`, observed at
2026-11-17 15:11:16 UTC: **all 12 checks passed**. The three dedicated proof
jobs completed compilation, exact-type acceptance, and axiom/dependency audits:

| Proof group | Public declarations | Exact-type examples | Hosted evidence |
| --- | ---: | ---: | --- |
| Actual prime/composite accounting | 16 | 9 | [Passed job](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44110847029/job/134135688923) |
| Cancellation scale and native-PNT obstruction | 11 | 8 | [Passed job](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44110847029/job/134135689038) |
| Finite exceptional sampling and ordinary complements | 14 | 7 | [Passed job](https://github.com/OVVO-Financial/RH_Lean/actions/runs/44110847029/job/134135688451) |

The subsequent DAG/documentation revision preserves all six proof and
acceptance files byte-for-byte and receives its own hosted checks. The dated
source receipt, exact SHA-256 hashes, job URLs, and evidence artifacts are
stored in `EV-PR-1143`; this receipt does not imply a human merge.

The new workflow `prime-phase-survivor.yml` checks the actual PR head with
Lean 4.34.1 and the repository's pinned Mathlib revision. It compiles each
complete original source dependency closure with warnings fatal, checks 24
explicit theorem types, and audits all 41 new public declarations.

The audit rejects unapproved terminal axioms and verifies transitive
dependencies on the original complete source, the native PNT, and the
native RH consumer where relevant. Only `propext`, `Classical.choice`, and
`Quot.sound` are allowed. Evidence artifacts include source hashes, exact
types, the checked commit, and the axiom/dependency results.

Lean execution is restricted to hosted GitHub Actions. Local source and DAG
checks do not count as kernel evidence. DAG certification of the new
declarations requires successful hosted proof checks; literature inputs
remain separate from proved Lean results, and open arithmetic targets retain
their status.

## 8. Registry entries and research disposition

The update adds 15 scoped nodes and five typed edges. The ten existing route
IDs remain unchanged. `SAT/signed-survivor` records the new direct native
consumer, with `OPEN-SIGNED-SQUARE-SURVIVOR` as its only unpaid premise.

| Registry entry | Meaning and status |
| --- | --- |
| `PROP-SQUARE-BLOCK-DEATH-BOUND` | The existing canonical death theorem, already on main; supporting infrastructure. |
| `PROP-NATIVE-PRIME-NUMBER-THEOREM` | The existing native PNT, already on main; the unconditional input for the component obstruction. |
| `PROP-SURVIVOR-PRIME-COMPOSITE-ACCOUNTING` | Exact cutoff, prime-count identity, composite correction, and source witnesses; proved in this green, unmerged PR. |
| `PROP-SURVIVOR-POINTWISE-LOCAL-EQUIVALENCE` | The complete-source local/pointwise equivalence and exact residual; proved in this PR. |
| `NOGO-PURE-PRIME-SURVIVOR-RH-SCALE` | The actual pure-prime component fails even the cubic squared bound; proved in this PR. |
| `OPEN-SIGNED-SQUARE-SURVIVOR` | The complete signed local-energy estimate, at a chosen fixed positive `Λ`; OPEN arithmetic. |
| `OPEN-SIGNED-SURVIVOR-POINTWISE` | Its proved-equivalent pointwise formulation; OPEN arithmetic. |
| `CONSUMER-SIGNED-SURVIVOR-RH` | Proved implication to Mathlib RH with the complete survivor premise retained. |
| `PROP-FINITE-SQUARE-EXCEPTIONAL-SAMPLING` | Proved finite-cardinality packing; prime persistence and analytic budgets are not supplied. |
| `PROP-ORDINARY-COMPOSITE-PRIME-DISCREPANCY` | Proved exact ordinary counting identities, separate from canonical signed ancestry. |
| `IFACE-PRIME-SQRT-PHASE`, `IFACE-PRIME-SQRT-FOUR-FIFTHS` | Established global literature results represented by explicit Lean hypotheses. |
| `FORMALIZE-PRIME-SQRT-PHASE` | Remaining formalization-completeness work for those classical inputs. |
| `LIT-ALMOST-ALL-SQUARE-PRIMES`, `FORMALIZE-ALMOST-ALL-SQUARE-PRIMES` | Established almost-all literature theorem and its remaining analytic formalization task. |

These are supporting identities, reductions, and a component obstruction.
They supply no independent subcritical arithmetic gain. In particular, the
new prime-component no-go theorem must not be applied to the complete signed
sum: retaining its composite correction is the point of the accounting.
