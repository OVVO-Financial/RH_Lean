# Obstruction to the fixed lower-Mertens coefficient synthesis

Audited source: `891298896eba423ba40ab4c316234d0523a04990` (merged #780).

**Status: a paper-level disproof using published external theorems, with an
exact-arithmetic certificate for the numerical constants. This is not a
kernel-checked Lean disproof.** No Lean definition, theorem, or assumption is
changed by this note. In particular, #780's compiled conditional consumer is
unaffected.

The specific proposition `LowOwnerStokesClipLowerMertensSynthesis` would imply

\[
\limsup_{x\to\infty}\frac{|M(x)|}{\sqrt{x}}<1.831.
\]

This contradicts Hurst's published unconditional result
\(\liminf M(x)/\sqrt{x}<-1.837625\). The obstruction concerns exactly the fixed
coefficients \(a_p=(M(p-1)-1)/\sqrt p\), with coefficient one in the synthesis
inequality. It does not refute the existing `K`-dependent final-Stokes target,
nor every possible coefficient construction or relaxed comparison.

The contradiction must account for the gaps between square endpoints. A
uniform bound on square endpoints alone cannot simply be substituted into
Hurst's result. Sections 5–7 supply that missing argument.

## 1. Source dictionary

Write

\[
X=R^2-1,\quad Q_R=\{q\text{ odd prime}:q^2<R\},\quad
Y_q=\lfloor X/q^2\rfloor,
\]

\[
G_R=M(R-1)-M(X)-\sum_{q\in Q_R}\frac{M(Y_q)}q,
\quad
h_R(n)=\sum_{q\in Q_R}\frac{\mathbf1_{n\le Y_q}}q.
\]

The diagonal is

\[
D_R=\sum_{n\le X}\mu(n)^2
       (\mathbf1_{n\ge R}+h_R(n))^2.
\]

The compiled endpoint-gap identity gives

\[
\mathrm{Clip}_R=|G_R|^2-D_R-T_R,
\qquad T_R\le4.
\tag{1}
\]

Exact declaration locations:

- `GLOBAL_RETURNED_CORE_STOKES_PHYSICAL_FRAME_BRIDGE.lean`:
  `lowOwnerCanonicalSignedStokesClipBoundary_eq_endpointGapNormSq_sub_diagonal_sub_terminal`,
  `lowOwnerStokesLowerMertensPrimeCoefficient`,
  `primePeriodReciprocalCoefficientEnvelope`, and
  `LowOwnerStokesClipLowerMertensSynthesis`.
- `GLOBAL_RETURNED_CORE_STOKES_ALL_ENDPOINT_MERTENS_LEDGER.lean`:
  `lowOwnerStokesAllEndpointMertensGap`.
- `GLOBAL_RETURNED_CORE_FIRST_OWNER_GRAM.lean` and
  `GLOBAL_RETURNED_CORE_WEIGHTED_GRAM.lean`: the diagonal and its site weight.
- `CANONICAL_ROUGH_Q2_TAIL_REDUCTION.lean`: the strict condition `q*q < R`.
- `GLOBAL_RETURNED_CORE_STOKES_TERMINAL_FRAME_API.lean`:
  `StokesTerminalFrame.exceptionalTerminalBoundary_le_four`.
  Its owner set is definitionally the same as the restricted terminal sum in
  `lowOwnerCanonicalSignedStokesTopTerminalBoundary_eq_terminalOwnerSum`.

Let \(E_R\) denote the literal coefficient envelope in the synthesis
proposition. Assuming that proposition, (1) gives

\[
|G_R|^2\le D_R+E_R+4.
\tag{2}
\]

## 2. The canonical coefficient envelope has a small fixed asymptotic constant

Set \(u_p=|M(p-1)-1|/\sqrt p\). The frequency of the period-\(p\) mode is
exactly \(1/p\). The unnormalized Dirichlet kernel in the repository is a sum
of \(X\) characters. For distinct odd primes,

\[
\frac{|D_X(1/p-1/q)|}{pq}
\le\frac{1}{pq\,|\sin(\pi(1/p-1/q))|}
\le\frac{1}{2|p-q|}.
\tag{3}
\]

Here \(0<|1/p-1/q|<1/2\), and \(\sin(\pi t)\ge2t\) on \([0,1/2]\).
Consequently the off-diagonal part satisfies

\[
E_R^{\rm off}\le\frac12\sum_{\substack{p,q<R\\p\ne q}}
                    \frac{u_pu_q}{|p-q|}
\le H_{R-1}\sum_{p<R}u_p^2,
\tag{4}
\]

where \(H_m=\sum_{j=1}^m1/j\). The second inequality uses
\(2u_pu_q\le u_p^2+u_q^2\) and bounds each row's reciprocal-distance sum by
\(2H_{R-1}\). These estimates concern the already-defined positive envelope;
no absolute value is inserted into the physical clip.

[Ramaré, Theorem 1.1](https://ramare-olivier.github.io/Maths/ElementaryConversion-11.pdf)
gives the unconditional estimate \(|M(x)|<0.013x/\log x\) for
\(x\ge1\,078\,853\). Thus
\(u_p^2=O(p/\log^2p)\). Splitting the sum at \(\sqrt R\), and even enlarging
the prime sums to integer sums, gives

\[
\sum_{p<R}u_p^2=O(R^2/\log^2R),\qquad E_R^{\rm off}=o(R^2).
\]

The diagonal is exact, so

\[
\frac{E_R}{R^2}\longrightarrow
c_*:=\sum_{p\text{ odd prime}}\frac{(M(p-1)-1)^2}{p^3}<0.092.
\tag{5}
\]

The accompanying certificate sieves through \(P=2\,000\,000\), rounds every
nonnegative rational summand upward, and obtains a prefix upper bound
\(0.091591002918\). For \(p>P\), monotonicity of \(x/\log x\) and Ramaré's
bound give

\[
|M(p-1)-1|\le0.014p/\log p.
\]

The additional `1` is absorbed because \(p/\log p>1000\) on this range.
Therefore the remaining tail is at most

\[
0.014^2\sum_{n>P}\frac1{n\log^2n}
\le\frac{0.014^2}{\log P}
<\frac{0.014^2}{13}.
\]

This proves \(c_*<0.091606079841<0.092\); no extrapolation from a measured
Mertens ratio is used.

## 3. Uniform squarefree counting and the diagonal bound

Define the convergent positive series

\[
\rho=\sum_{q\text{ odd prime}}q^{-2},\quad
\tau=\sum_{q\text{ odd prime}}q^{-3},\quad
\kappa=\sum_{p,q\text{ odd prime}}
          \frac1{pq\max(p,q)^2}.
\]

The certificate proves

\[
\rho<0.2023,\quad0.0497<\tau<0.0498,\quad\kappa<0.027.
\tag{6}
\]

For example, prime sums through \(100\,000\) bound \(\rho,\tau\), with the
remaining tails enlarged to all integers and integrated. For \(\kappa\), use

\[
\kappa=\sum_q q^{-4}
  +2\sum_q q^{-3}\sum_{p<q}p^{-1}.
\]

After \(L=1000\), the tail is at most
\(1/(3L^3)+(\log L+3/2)/L^2\). The certified upper bound is below
\(0.025801092\).

The finite squarefree mask for primes up to 2000 has density

\[
\prod_{p\le2000}(1-p^{-2})<\delta:=0.608.
\]

By periodic counting, there is a fixed finite constant \(C_0\) such that
**every** integer interval of length \(h\) contains at most
\(\delta h+C_0\) squarefree integers. This is a deterministic finite-wheel
bound, not a transfer of a global density onto an arithmetically selected
population. Its possibly enormous fixed endpoint error is harmless in the
limits below.

Expand the positive diagonal in (1) and apply this counting bound to each
literal prefix. Discarding the lower cutoff in its nonnegative cross term
only increases the result. With \(b_R=\sum_{q\in Q_R}1/q=O(\log R)\),

\[
D_R\le\delta X(1+2\tau+\kappa)+C_0(1+b_R)^2.
\]

In particular,

\[
\limsup_R D_R/R^2
\le0.608(1+2\cdot0.0498+0.027)=0.6849728.
\tag{7}
\]

The same counting bound also gives, uniformly in integer endpoints,

\[
|M(v)-M(u)|\le\delta|v-u|+C_0.
\tag{8}
\]

## 4. What the proposed synthesis would force on the gap

Combining (2), (5), and (7),

\[
\limsup_R |G_R|^2/R^2
\le0.6849728+0.092=0.7769728<0.882^2.
\]

Hence \(|G_R|\le0.882R\) for all sufficiently large \(R\). This conclusion
uses the proposed synthesis; the bounds on the envelope and diagonal do not.

## 5. The square-endpoint limsup is finite (no circular limsup subtraction)

First establish a coarse uniform bound by strong induction on \(R\).
For each \(q\in Q_R\), choose \(s_q\) nearest to \(R/q\). Then
\(1\le s_q<R\), and

\[
\sum_{q\in Q_R}\frac{s_q}{q}
\le R\rho+\tfrac12b_R\le R/4
\]

eventually. The elementary bound \(|\mu|\le1\) and the distance estimate in
the next section also give

\[
\sum_{q\in Q_R}\frac{|M(Y_q)-M(s_q^2-1)|}{q}\le R/3
\]

eventually. Since \(|M(R-1)|\le R\) and \(|G_R|\le R\) eventually, the
induction assumption \(|M(s^2-1)|\le A_0s\) at smaller \(s\) yields

\[
|M(R^2-1)|\le(2+A_0/4+1/3)R\le A_0R
\]

for \(A_0\ge4\). Enlarge \(A_0\) once to cover the finite initial range.
Thus

\[
A:=\limsup_{R\to\infty}|M(R^2-1)|/R<\infty.
\]

## 6. Preserve the odd-prime improvement in each daughter shell

Because \(q\) is odd and \(R\) is an integer,

\[
|R/q-s_q|\le(q-1)/(2q).
\]

The floor in \(Y_q\) and the `-1` square-endpoint convention give the uniform
algebraic estimate

\[
|Y_q-(s_q^2-1)|
\le\frac Rq(1-1/q)+2.
\tag{9}
\]

Indeed, put \(t=R/q\), \(e=s_q-t\). Then
\(|t^2-s_q^2|\le2t|e|+e^2\le t(1-1/q)+1/4\), and replacing
\(t^2\) by \(\lfloor t^2-q^{-2}\rfloor+1\) costs less than one.

Apply (8) to (9). Uniformly over the low-owner set,
\(s_q\ge\sqrt R-1/2\to\infty\), so the definition of the finite \(A\)
applies to every daughter simultaneously. Dividing the column by \(R\), its
limsup is at most

\[
A\rho+\delta(\rho-\tau).
\]

All fixed endpoint errors sum to \(O(b_R)=o(R)\). Ramaré's estimate also
gives \(M(R-1)=o(R)\). The exact formula for \(G_R\) therefore implies

\[
A\le0.882+A\rho+0.608(\rho-\tau),
\]

and hence, using (6),

\[
A\le
\frac{0.882+0.608(0.2023-0.0497)}{1-0.2023}
<1.223.
\tag{10}
\]

Replacing the odd-prime shell factor \(\rho-\tau\) by \(\rho\) would lose
enough to obscure the contradiction. It must be retained.

## 7. Return to all integer endpoints and contradict Hurst

For arbitrary integer \(n\), take \(s\) nearest to \(\sqrt{n+1}\). Then

\[
|n-(s^2-1)|\le\sqrt{n+1}+1/4,\qquad s/\sqrt n\to1.
\]

Equations (8) and (10) give

\[
\limsup_{n\to\infty}\frac{|M(n)|}{\sqrt n}
\le A+0.608<1.223+0.608=1.831.
\tag{11}
\]

[Hurst, Theorem 6.1](https://arxiv.org/pdf/1610.08551) proves
\(\liminf_{x\to\infty}M(x)/\sqrt x<-1.837625\). His Theorem 4.2 explicitly
does not assume RH. The integer and real endpoint limsups agree because
\(M(x)=M(\lfloor x\rfloor)\). Thus (11) contradicts that published result.

## Consequence and verification boundary

The literal fixed-coefficient synthesis with constant one cannot be the final
missing true theorem, assuming the cited published results. The coefficient
budget theorem remains valid: it bounds a well-defined candidate family.
It does not identify that family as coefficients of the signed physical clip.
The two-toggle identity likewise remains valid; it changes neither (1) nor
the contradiction.

The conclusion here is specific. A comparison with an additional constant or
remainder requires a new numerical audit. This note does not supply a faithful
alternative synthesis or an RH proof.

Run `python3 scripts/stokes_lower_mertens_synthesis_audit.py` to reproduce the
finite and rational checks. The script also independently checks the Möbius
divisor identity through 2000 and tests (9) through root 3000. Those finite
checks support the implementation; the all-scale reasoning is written above.
Neither the external theorems nor this analytic argument have been imported
into Lean, so this must not be advertised as a kernel-certified no-go theorem.
