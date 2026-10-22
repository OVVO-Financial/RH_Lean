# RH_Lean agent daily report - 2026-10-21 / RH | Analytic Type II

**Status:** COMPLETED  
**Run:** 2026-10-21 22:26 EDT scheduled invocation  
**Canonical objective:** \`VFCanonicalSquareVonKochStatement\` remains OPEN  
**Campaign status:** \`INCOMPLETE; NO INDEPENDENT 7/8 PROOF\`  
**Result classes:** \`PAPER_PROOF / QUANTITATIVE TRANSFER\`, \`EXACT COUNTEREXAMPLE\`, \`NO_NEW_GLOBAL_BOUND\`

## A. Most important analytic development

The complete-dual/class-alias mechanism now has an explicit transfer theorem for the source defect that the current OAI correspondence actually exposes: coefficients may vary with the physical row.

For a fixed reference source, the theorem separates:

1. complete-dual same-class alias covariance;
2. restricted/weighted character-kernel error;
3. row-dependent coefficient drift.

The second-moment drift loss is
\[
  s_2(\eta,L)=\eta(2L+\eta),
\]
and the fourth-moment drift loss is
\[
  s_4(\eta,L)=
  \eta(2L+\eta)\big((L+\eta)^2+L^2\big).
\]
Here \(L=\|a\|_1/\|a\|_2\), while
\(\eta=\max_r\|a^{(r)}-a\|_1/\|a\|_2\).

Thus \(s_4=4\eta L^3+O(\eta^2L^2+\eta^3L+\eta^4)\). A qualitative statement that the row coefficients are "close" is not enough. To preserve a relative \(U^{-\sigma}\) fourth-moment gain one needs, at minimum, the combined restricted-kernel and coefficient-drift bill at that same scale; in the small-drift regime this requires
\[
  \eta L^3=O(U^{-\sigma}).
\]
If there are \(n\) atoms, \(L\le\sqrt n\), so the generic sufficient scale is
\(\eta n^{3/2}=O(U^{-\sigma})\).

This is a quantitative transfer and inverse diagnostic, not a proof that the actual OAI source satisfies the required kernel or drift estimates.

## B. Authority, source, and continuity

Final authority refresh:

- \`main@66af9b34c082485872815ece9a7721606381c07f\`.
- \`AGENTS.md\` blob \`20bff52d6784c17d4a7d6ac731f4a71c2bdad8a6\`.
- \`CURRENT_PROOF_CONTRACT.md\` blob \`2fa9931dcdc1fc8a816aefb8aa348db12ee9a384\`.
- Native replication protocol blob \`53194dc3ae106be363bc22cf85a88bac4a3b2e6e\`.
- Native local compensation blob \`6956bb67b34fdeec288a020d9aa1350488832852\`.
- Complete-residue trace source blob \`fb4bf3618c8644e80818062ece5050506db9d9b2\`.
- Actual weighted NNS covariance source blob \`2595fc93d1faf4b7ec1ad14dbabb9d3db857904d\`.
- External handoffs blob \`038018145c0fddb2f6306c0712373adf9cd1ea52\`.

Continuity consumed:

- 2026-10-20 Analytic blob \`1c0c7e1c6561a95fc0c0ca8c3c6e99a829693051\` as \`YESTERDAY=CARRY_FORWARD\`.
- 2026-10-21 Coordinator \`fb11676896cefe49fc25a5b03b16e278085cc8a5\`.
- Owner \`f2dbb2c646afce789071902fcb5e9f05c4bed8b2\`.
- Census \`b7ea2642bb7713e8a1685dc77c5a3b3b0f1cc800\`.
- Referee \`e6ef7fa0ebffeea4643b9e892591156d6cd0c1fb\`.
- Lean \`6c0d5af5ad0b00608643513585bd6a8c59207098\`.
- 2026-10-21 Wheel is absent: \`TODAY=PENDING\`; 2026-10-20 Wheel blob \`16519e3f2bb2ee0da08ae843f5b3311c2fb5276c\` is \`YESTERDAY=CARRY_FORWARD\`.

The live campaign still requires the native Stage-I 11/12 probe, actual compensated source, inverse second/plain fourth moments, principal/ramified/exceptional restoration, common-probe assembly and terminal nonvanishing argument. Exact NNS or Euler identities are not an analytic saving.

## C. Claim \`20261021-analytic-1\`: row-stable restricted-kernel transfer

### C.1 Exact objects and quantifiers

Let \(I\) be a nonempty finite atom set, \(G\) a finite abelian group, and
\(\phi:I\to G\). Let \(R\) be a finite row set with weights
\(\lambda_r\ge0\), \(\sum_r\lambda_r=1\), and unitary characters
\(\chi_r:G\to\mathbb C^\times\).

Choose a reference coefficient vector \(a=(a_i)_{i\in I}\) with
\[
 E=\sum_i|a_i|^2>0,\qquad
 L={\sum_i|a_i|\over\sqrt E}.
\]
At row \(r\), the actual coefficient vector is \(a^{(r)}\), with
\[
 \max_r\sum_i|a_i^{(r)}-a_i|\le\eta\sqrt E.
\]
Define
\[
 Y_r=\sum_i a_i\chi_r(\phi(i)),\qquad
 X_r=\sum_i a_i^{(r)}\chi_r(\phi(i)),
\]
and actual moments
\[
 M_2=\sum_r\lambda_r|X_r|^2,\qquad
 M_4=\sum_r\lambda_r|X_r|^4.
\]

Let \(K_2\) be the restricted weighted Gram on \(I\), and \(P_2\) the
complete-dual class projector:
\[
 K_2(i,j)=\sum_r\lambda_r\chi_r(\phi(i))\overline{\chi_r(\phi(j))},
 \qquad
 P_2(i,j)=1_{\phi(i)=\phi(j)}.
\]
Let \(\delta_2=\|K_2-P_2\|_{\rm op}\).

On ordered atom pairs define \(K_4\) and \(P_4\) by the same formulas with
class product \(\phi(i)\phi(j)\). Let
\(\delta_4=\|K_4-P_4\|_{\rm op}\).
These are exact finite operator norms; no asymptotic or positivity of
off-diagonal entries is assumed.

Finally set
\[
 A_{\rm alias}=
 \sum_g\sum_{\substack{i\ne j\\\phi(i)=\phi(j)=g}}
       \operatorname{Re}(a_i\overline{a_j}).
\]
Then \(E+A_{\rm alias}=\sum_g|\sum_{\phi(i)=g}a_i|^2\ge0\).

### C.2 Forward transfer

Let \(C_2\) and \(C_4\) be the complete-uniform-dual second and fourth
moments of the fixed reference vector. Then
\[
 |M_2-C_2|\le(\delta_2+s_2(\eta,L))E,                 \tag{T2}
\]
\[
 |M_4-C_4|\le(\delta_4+s_4(\eta,L))E^2.               \tag{T4}
\]

Consequently, any independently proved complete-dual estimate transfers to
the actual source only after adding the displayed restricted-kernel and
row-drift bills. All constants are explicit and uniform once
\(\delta_k,\eta,L\) are controlled.

### C.3 Inverse consequence

Complete-dual orthogonality gives
\[
 C_2=E+A_{\rm alias},\qquad C_4\ge C_2^2.
\]
Therefore:

- if \(M_2\le\rho_2E\), then
\[
 A_{\rm alias}\le
   (\rho_2+\delta_2+s_2-1)E;                           \tag{I2}
\]
- if \(M_4\le\rho_4E^2\), then
\[
 A_{\rm alias}\le
   \left(\sqrt{\rho_4+\delta_4+s_4}-1\right)E.          \tag{I4}
\]

In particular, a strict contraction forces quantitatively negative
same-class alias covariance only when the kernel and coefficient-drift losses
are smaller than the proposed margin. This extends Coordinator claim
\`20261021-coordinator-2\` to the restricted, row-dependent source interface.

## D. Proof

For each row,
\[
 |X_r-Y_r|\le\sum_i|a_i^{(r)}-a_i|\le\eta\sqrt E,
 \quad |Y_r|\le L\sqrt E,\quad |X_r|\le(L+\eta)\sqrt E.
\]
Hence
\[
 \big||X_r|^2-|Y_r|^2\big|
 \le |X_r-Y_r|(|X_r|+|Y_r|)
 \le s_2E,
\]
and
\[
 \big||X_r|^4-|Y_r|^4\big|
 \le |X_r-Y_r|(|X_r|+|Y_r|)(|X_r|^2+|Y_r|^2)
 \le s_4E^2.
\]
Averaging preserves both bounds.

For the fixed reference vector,
\[
 \sum_r\lambda_r|Y_r|^2=\langle a,K_2a\rangle,
 \quad C_2=\langle a,P_2a\rangle.
\]
The operator norm gives an additional error at most \(\delta_2E\).

For the fourth moment use the pair vector
\(v_{ij}=a_ia_j\). Its squared norm is
\[
 \|v\|_2^2=\left(\sum_i|a_i|^2\right)^2=E^2.
\]
The restricted and complete fourth moments are
\(\langle v,K_4v\rangle\) and \(\langle v,P_4v\rangle\), so their difference
is at most \(\delta_4E^2\). This proves (T2) and (T4).

Writing \(b_g=\sum_{\phi(i)=g}a_i\) gives
\(C_2=\sum_g|b_g|^2=E+A_{\rm alias}\).
For the complete uniform dual,
\[
 C_4=\mathbb E_{\chi\in\widehat G}
       \left|\sum_gb_g\chi(g)\right|^4
 \ge
 \left(\mathbb E_{\chi\in\widehat G}
       \left|\sum_gb_g\chi(g)\right|^2\right)^2=C_2^2
\]
by Cauchy-Schwarz. Combining these inequalities with (T2)/(T4) proves
(I2)/(I4). Every sum is finite.

A 1,000-trial randomized numerical check reproduced (T2)/(T4); this is only
a sanity check, not evidence for the all-scale source hypotheses.

## E. Quantitative accounting and detector relevance

There are no omitted boundary terms inside this finite theorem. Every loss is
one of:

- complete-dual alias energy \(A_{\rm alias}\);
- restricted row-family defects \(\delta_2,\delta_4\);
- coefficient drift \(s_2,s_4\).

The constants are absolute in the normalized statement. Parameter dependence
enters explicitly through \(L,\eta,\delta_2,\delta_4\).

For an atom count \(n=|I|\), \(1\le L\le\sqrt n\). In the small-drift regime:
\[
 s_2=2\eta L+O(\eta^2),\qquad
 s_4=4\eta L^3+O(\eta^2L^2+\eta^3L+\eta^4).
\]
Thus growing labelled carriers magnify coefficient instability. A bound
\(\eta=o(1)\) without a rate is insufficient if \(L\) grows, and even a fixed
strict contraction is insufficient for a desired \(U^{-\sigma}\) relative
gain unless the full error budget decays at the required scale.

The theorem is weaker than a genuine OAI moment estimate and independent of
the seven-eighths conclusion. It identifies a necessary transfer budget; it
does not assume or imply zeta nonvanishing.

## F. Source applicability

The draft #1003 coefficient audit has the actual shape
\[
 a_{J,p,r}(j,t)=c_J(p)\,(\text{slot windows})\,
 B_{J,p,r}(j,t)\,(\text{log phases})\,\rho_J(j,t),
\]
where \(B_{J,p,r}\) contains physical-row weight, corrected completed theta
data and the row monoid. Thus the coefficient genuinely varies with
\(r,j,t\). No theorem currently supplies a fixed reference vector with a
bound on \(\eta\), much less \(\eta L^3=O(U^{-\sigma})\).

The actual weighted NNS theorem on main correctly keeps \(a(u,I)\)
row-dependent. Therefore neither the complete-residue moments nor the
fixed-weight chi-square transfer from \`20261020-analytic-1\` can be applied
directly by declaring one nonnegative bucket measure. One must either:

1. prove the explicit row-stability and restricted-kernel estimates in
   (T2)/(T4); or
2. estimate the genuinely row-dependent four-point kernel directly, retaining
   all \(r,j,t,J,p\) labels and cross-height terms.

The post-integration NNS equality in draft #1003 is exact, but consuming the
already proved OAI pointwise bound reproduces its published exponent only. It
does not establish a new \(\sigma>0\).

## G. Falsification

The fixed-source hypothesis cannot be dropped.

Take two atoms in distinct classes \(g_1,g_2\). At each row \(r\), set
\[
 a^{(r)}_1=1,\qquad
 a^{(r)}_2=-{\chi_r(g_1)\over\chi_r(g_2)}.
\]
Then
\[
 a^{(r)}_1\chi_r(g_1)+a^{(r)}_2\chi_r(g_2)=0
\]
for every row, so every actual second and fourth moment vanishes even though
the class map is injective and each row has raw energy \(2\). This exact
counterexample was checked for all sixth-root characters.

Therefore class injectivity, complete-residue trace moments, or a fixed
alias calculation says nothing by itself about arbitrary row-dependent
coefficients. The required stability or direct weighted-kernel theorem is a
real hypothesis, not technical bookkeeping.

The theorem also does not contradict Census claim \`20261021-census-1\`:
shellwise excess can have either sign because no small uniform
\(\delta_k,\eta\) has been established on that carrier.

## H. Handoffs

**Coordinator:** insert (T2)/(T4) after the fixed-source alias diagnostic.
Any dependency edge from complete-residue moments to the actual OAI moment
must expose \(\delta_2,\delta_4,\eta,L\), or replace them by a direct
row-dependent kernel theorem.

**Owner Payment:** use the exact #1003 labels to decide whether a natural
reference coefficient exists. If so, bound the full \(\ell^1\) drift,
including physical-row, corrected-completed, Gaussian-density and log-phase
variation; a norm-only or rational-norm pushforward is insufficient.

**Finite Wheel:** determine whether the 2/1/0 zero masks and conjugate-product
constraint reduce \(L\) or the pair-kernel operator norm uniformly. Today's
Wheel report remains pending.

**Prime Census:** compute \(L,\eta,\delta_2,\delta_4\) on exact source slices,
not only trace histograms. Normalize fourth-order error by
\(\eta(2L+\eta)((L+\eta)^2+L^2)\).

**Adversarial Referee:** audit the pair-kernel operator norm and the source
dependence on \(r,j,t\). Reject any fixed-weight collision claim that silently
freezes the actual physical core.

**Lean Verification:** after review, the finite theorem can be formalized with
Finset sums, complex triangle inequalities and operator-norm hypotheses. Do
not instantiate an unproved \(U^{-\sigma}\) kernel/drift premise and label it
an analytic moment proof.

## I. PR and GitHub Actions audit

Open draft stack at final check:

- #1000 head \`9edc4ad3d1dd12bb23a60660fb1945237149f821\`: 10/10 listed workflows completed successfully.
- #1001 head \`5056d7938e46b53e7e497d58c2a7e6db450ba4be\`: 6/6 completed successfully.
- #1002 head \`a8a46299f4283407e1d8ddb0c041104097fcc222\`: 6/6 completed successfully.
- #1003 head \`955cfaf098aa23d4a9e9bea8f910ffa481521b59\`: 6/6 completed successfully.

These are stacked human-merge drafts. Green CI verifies their exact structural
Lean content; it does not supply a new source moment exponent. #1003 source
audit blob \`e4eb9dd80308f9b12a4b8f8a54c041a34d4e3729\` preserves the exact
GaussianSubset coefficient and the full integrated principal term, but the
OAI-to-native type intertwining and improved quantitative moment remain open.

No PR, merge, workflow rerun, main source, schedule or permission state was
changed in this execution.

## J. Resume capsule

- New claim \`20261021-analytic-1\`: explicit second/fourth transfer and inverse
  theorem with restricted-kernel defects and row-dependent coefficient drift.
- Exact losses:
  \(s_2=\eta(2L+\eta)\) and
  \(s_4=\eta(2L+\eta)((L+\eta)^2+L^2)\).
- Exact counterexample: arbitrary row dependence permits zero moment on an
  injective two-class source; fixed alias energy alone is inapplicable.
- Strongest required scale for a relative \(U^{-\sigma}\) fourth-moment gain:
  \(\delta_4+s_4=O(U^{-\sigma})\), hence approximately
  \(\eta L^3=O(U^{-\sigma})\).
- First source blocker: construct the actual fixed-reference adapter or retain
  the full row-dependent OAI coefficient.
- First analytic blocker: prove a moving-conductor restricted pair-kernel bound
  with physical weights and all principal/ramified/exceptional/cross-height
  sectors.
- Stage I 11/12, genuine inverse second/plain fourth moment, independent native
  7/8, canonical VF, and RH remain OPEN.
- Campaign status: \`INCOMPLETE; NO INDEPENDENT 7/8 PROOF\`.

## K. Publication verification

Early \`IN_PROGRESS\` checkpoint commit:
\`8e6b2317e5877542070e7049e313a40d65b8c292\`.

Substantive completion commit: `16d5cfba4cb5d109b7c1e0ff4d28dd538b140b9a`; returned content blob: `3da19156b35045e28abaccffcae560e9aa1337f5`. Final metadata update only; mathematical content and status are unchanged.
