# #919 — exact signed quotient cutoffs and delayed arithmetic return

**Proof boundary:** unconditional finite arithmetic identities and numerical
censuses, not the uniform mixed-moment estimate or the historical first-bad
Sector Six payment.

## Literal quotient ledger

With \(X=R^2-1\), \(a^{(6)}(m)\) the *constructed* excluded-six norm
coefficient and \(C_\chi(n)=\sum_{1\le d\le n}\chi_{-3}(d)\), set

\[
k(t)=C_\chi(t)-C_\chi(\lfloor t/3\rfloor)
-C_\chi(\lfloor t/4\rfloor)+C_\chi(\lfloor t/12\rfloor),\qquad
B_X(t)=\sum_{\substack{1\le m\le X\\\lfloor X/m\rfloor=t}}a^{(6)}(m).
\]

The new module \`research/VF_MID_919_QUOTIENT_SIGNED_RETURN.lean\` proves,
**for every integer \(X\ge12\)**,

\[
\boxed{M(X)=\sum_{t=1}^X k(t)B_X(t).}
\]

No occurrence has been averaged, discarded or absolute-valued. The actual
period-36 kernel has an explicit integer primitive \(F\) satisfying

\[
F(n)-F(n-1)=k(n),\qquad -4\le F(n)\le4
\]

for \(n>0\), with \(F(0)=0\). Abel summation and \(B_X(X+1)=0\)
give the **exact signed return identity**

\[
\boxed{M(X)=\sum_{t=1}^XF(t)\,[B_X(t)-B_X(t+1)].}
\]

The elementary bound \(|M(X)|\le 4V_X\) follows, where

\[
V_X=\sum_{t=1}^X|B_X(t)-B_X(t+1)|.
\]

**Nothing in the proof bounds \(V_X\) at RH scale**; that is a distinct
arithmetic question. The finite quotient-bucket identity and bounded
primitive do not establish a uniform moment estimate.

## Each norm eventually returns its own signed coefficient

The quotient period is **not** a period in the norm \(m\). For any \(m>0\)
and starting quotient \(a\), the full physical cutoff clock has

\[
\boxed{\sum_{x=ma}^{m(a+36)-1}k(\lfloor x/m\rfloor)
=m\sum_{j=0}^{35}k(a+j)=0.}
\]

The corresponding all-start and 36m-clock theorems in the new Lean module
retain each norm occurrence and use literal integer division. For the
physical norm coefficient to have entered the summation, take \(a\ge1\).

**Crucial timing limitation:** the restoring cycle takes \(36m\)
successive cutoff endpoints. A norm born near \(X=R^2\) need not complete
its return before the next square endpoint, or before a hypothetical
first-bad wall crossing. A future return cannot be spent as historical
payment without an additional argument. Distinct norms have
unsynchronized clocks, so summing their eventual zero means does not
control the instantaneous Mertens sum or original Sector Six Gram.

## Independent exact numerical evidence

The script \`scripts/vf919_quotient_signed_return_probe.py\` starts from
the already dual-checked Euler/convolution coefficients, assigns each
norm to its **one** actual integer quotient, verifies both signed
identities, and measures absolute mass only *after* those identities.

| R | M(R²−1) | Raw absolute norm mass | After signed quotient buckets | After 36-quotient packets | Quotient variation V |
|---:|---:|---:|---:|---:|---:|
| 317 | −28 | 22,026 | 670 | 104 | 1,507 |
| 548 | +234 | 65,796 | 1,100 | 384 | 3,296 |
| 1027 | +367 | 231,177 | 2,535 | 901 | 7,622 |
| 3000 | −340 | 1,972,000 | 9,288 | 1,810 | 24,671 |

The first three rows run in the default regression; \(R=3000\) runs with
\`--extended\`. All figures are exact integers. The script also checks
the full 36m temporal return for \(m=1,7,13,31,97,503\) and several
starting quotients.

**Adversarial signs:** whole period-36 packets can be positive *or*
negative. At \(R=1027\) the first packet contributes \(+333\); at
\(R=317\), the sixth contributes \(+16\). A universal claim that each
packet is independently restoring is false.

The observed \(V_{R^2-1}/(R\log R)\) at these four roots is roughly
\(0.83,0.95,1.07,1.03\). This motivates examining variation but is **not**
a bound for arbitrary \(R\), and cannot be substituted for one.

## Exact relevance to the original owner-two / Sector Six target

PR #919 already proves the full native p=2 Gram
\(2G_R=-2\Re(H_R\overline{J_R})\).
Its clipped boundary contains the genuine \(M(R^2-1)\). The new ledger
therefore identifies how its **top clipped Möbius input** changes with
the quotient cutoffs.

It does **not** by itself reassemble the returned-child leg
\(J_R\), its \(n\mapsto2n\) cutoff, the original VF square-band weights or
the once-only historical parent charges. It does not identify OpenAI's
single centered Hecke-ideal rectangle with the native weights, nor
prove a uniform one-sided signed cross estimate.

The decisive next object is the **history-conditioned, truncated**
signed return in the *complete* \(H_R,J_R\) cross matrix, before any
absolute-value or packetwise sign relaxation. The finite return clock
and its limitations must be carried through that identification, not
treated as an RH proof.

## CI

The principal-coefficient workflow imports the new module, compiles
with warnings fatal, audits every new theorem using only standard
Lean axioms, and runs the numerical regression. Green CI on the
reviewed HEAD is the authority for kernel verification. The actual
Eisenstein-ideal semantic import remains separate (OpenAI Lean 4.34
versus RH_Lean Lean 4.24).
