# Independent review and strengthened unconditional payment no-go — 2026-10-14

**Origin:** independent review of the externally published Claude seven-function cycle and of its [PR #938](https://github.com/OVVO-Financial/RH_Lean/pull/938), [PR #939](https://github.com/OVVO-Financial/RH_Lean/pull/939). Not one of the eight scheduled agent reports.  
**Research label:** **PAPER_PROOF** for the new all-scale Littlewood consequence; **direct source/CI verification** for the reported formal propositions. **No Lean formalization of Littlewood or the new limsup assertion is claimed here.**  
**Authoritative source checked:** main \`fcccdb32559d762dc5296dc519929f053f0fdf95\`; \`AGENTS.md\` blob \`709ad61bf4555fe4f2c92af3fd42f3994798c8bf\`; contract blob \`f6e8dc6813ec63974489c26b0c383e34203f0aa9\`.  
**Live PR heads at review:** #938 \`e2a2f39b9999652be2207bb7afa083d67f8efb78\`; #939 \`7b9385069c78f6f4001a0288ca702bd0db5a21c3\`, both open and review-ready. Exact-target CI runs \`38564233734\` and \`38565494102\` had successful jobs.

## Claim EXT-20261014-5: the normalized original #915 payment has unconditional limsup exactly 1

**PAPER_PROOF from established Littlewood oscillation, Brun–Titchmarsh, and the repo's exact original definitions. Not proven in Lean here.**

Use the *raw physical* square endpoint defect, independent of the public constant sqrt(2) phase:

\`\`\`text
D_R    := pi(R^2) - F_R                        (R >= 8)
P_R    := # genuine primes in strict square block R
m_R    := (2R+1)/log(R^2+R+1/2)
w_R    := m_R/R
beta_R := w_R*R + (1-2*w_R)*P_R
        = sum_{n in odd candidate seats R} |original signed seat charge(R,n)|
T_R    := (|D_R| + beta_R)^2
S_R    := D_{R+1} = D_R + P_R - m_R
N_R    := S_R^2/T_R
\`\`\`

By \`vfMid915SourcePaymentAt_iff_twoParameter\` in #939, \`T_R\` is exactly \`vfMidFirstBadZeroTargetTotalMass R\`, and \`S_R\` is exactly \`vfMidFirstBadDecompressedHistoricalSource R\`. No alternate global NNS denominator is being substituted.

**Claim:**
\`\`\`text
forall R >= 8:  0 <= N_R <= 1,
limsup_{R -> infinity} N_R = 1.
\`\`\`

In particular, for every constant \`c < 1\` and every integer \`R0\`, there is some \`R >= R0\` with \`N_R > c\`; indeed there are infinitely many. Thus \`2*S_R^2 <= T_R\` (equivalent to \`N_R <= 1/2\`) is **false infinitely often without the first-bad hypothesis**, and NO fixed improved universal payment ratio smaller than 1 is possible for this unchanged physical denominator.

### Proof with all dependencies exposed

1. **Pointwise triangle ledger (elementary, using compiled identities):** signed odd-seat charge sums to \`m_R - P_R\`; the absolute sum is \`beta_R >= |m_R-P_R|\`. Therefore \`S_R=D_R + P_R-m_R\` and
   \`\`\`text
   |S_R| <= |D_R|+beta_R <= |S_R|+2*beta_R.
   \`\`\`
   At \`R>=8\`, \`beta_R>0\`, so
   \`\`\`text
   (|S_R|/(|S_R|+2*beta_R))^2 <= N_R <= 1.
   \`\`\`
   The left side is defined even when \`S_R=0\`.

2. **Bound the actual block's absolute mass (known Brun–Titchmarsh):**
   \`m_R=O(R/log R)\` and the square-block length is \`2R+1\`. The short-interval Brun–Titchmarsh upper bound gives \`P_R=O(R/log R)\`, unconditionally. Therefore
   \`0<beta_R<=m_R+P_R=O(R/log R)\`.

3. **Large signed endpoint defects exist on square endpoints (known Littlewood):**
   \`\`\`text
   pi(x)-li(x) = Omega_+ (sqrt(x)*logloglog(x)/log(x))
              = Omega_- (sqrt(x)*logloglog(x)/log(x)).
   \`\`\`
   For any large real \`x\`, choose \`R=floor(sqrt x)\`. The gap between \`x\` and \`R^2\` is at most \`2R+1\`; Brun–Titchmarsh bounds the intervening change of \`pi\` by \`O(R/log R)\`, and elementary logarithmic integration bounds the change of \`li\` by the same order. The compiled uniform \`VF_can - Li_2 = O(1)\` quadrature yields \`F_R-li(R^2)=O(1)\` (additive normalizations differ by a fixed constant). Hence the Littlewood peaks transfer to squares at error \`O(R/log R)\`, so
   \`\`\`text
   limsup_{R -> infinity} |D_R| / (R/log R) = infinity.
   \`\`\`

4. **Limit superior of physical normalized energy:** choose unbounded \`R_j>=9\` with \`|D_{R_j}|/(R_j/log R_j)->infinity\`; set \`r_j=R_j-1\`. Then \`beta_{r_j}=O(r_j/log r_j)\` and \`|S_{r_j}|=|D_{R_j}| >> beta_{r_j}\`, whence \`beta_{r_j}/|S_{r_j}| -> 0\`. The pointwise sandwich in step 1 yields \`N_{r_j}->1\`. Combined with \`N_R<=1\`, this proves \`limsup N_R=1\`.

This strengthens the Claude handoff's \`CL-20261014-11\`, which established only infinitely many failures of \`N_R<=1/2\`. The new result explains the full asymptotic limiting obstruction: **the untouched original absolute normalization loses every fixed fraction of margin infinitely often**. The conclusion is compatible with RH and does **not** produce a first-bad(2) event. Under RH that conditional antecedent may be empty; the no-go addresses the unconditional everywhere payment law.

### Existing / external inputs

- \`research/VF_MID_FIRST_BAD_NORMALIZED_PARTIAL_MOMENT.lean\`, \`vfMidFirstBadZeroTargetTotalMass_eq\`.
- \`research/VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean\`, \`vfMidActualPrimeFirstBadAt_two_succ_victory_of_sourceInlet\`.
- #939 \`research/VF_MID_915_SOURCE_PAYMENT_CONTENT_AUDIT.lean\`, \`vfMid915SourcePaymentAt_iff_twoParameter\`, \`vfMidActualPrimeEndpointDefect_succ_eq_add_blockSupply\`, \`vfMidOddSignedSeatCharge_absSum_eq\`.
- Classical Littlewood omega theorem, e.g. [Kotnik, The prime-counting function and its analytic approximations](https://www.researchgate.net/publication/220391043_The_prime-counting_function_and_its_analytic_approximations) or [Bays–Hudson, A new bound for the smallest x with pi(x)>li(x)](https://www.researchgate.net/publication/2122330_A_new_bound_for_the_smallest_x_with_pix_lix).
- Montgomery–Vaughan short-interval Brun–Titchmarsh [The large sieve, *Mathematika* 20 (1973)](https://doi.org/10.1112/S0025579300004708).

## Review corrections and limits

- **SOURCE-SPLICE-1 must be distinguished from the payment estimate.** The direct arithmetic *equality/identification* between real signed source occurrences and a Sector-Six ledger could be an unconditional lemma **without itself implying RH**. Its proposed *quantitative payment inequality* is RH-hard. #939 proves content/equivalence of the payment, not that every possible exact source-to-ledger identity is RH-equivalent or impossible.
- **The historical local paired \(G(M,S)\) model is not the native #915 denominator.** #939 confirms \`T_R=(|D_R|+current absolute seat sum)^2\`; the entire older history is compressed inside \`|D_R|\`. The previous EXT-20261014-3 isolated negative pair inequality remains algebraically correct but DOES NOT establish failure of this globally defined payment by itself.
- **StrongPNT formalization is not the strongest known unconditional estimate.** A de la Vallée Poussin \`x*exp(-a*sqrt(log x))\` bound is an achievable *weaker* baseline; the classical Vinogradov–Korobov \`x*exp(-c*(log x)^(3/5)*(loglog x)^(-1/5))\` is sharper. Neither reaches the von-Koch RH scale. A suggestion to formalize the former should be labeled **repository-engineering progress**, not RH advance.
- **No prohibition on arithmetic proof methods follows from this audit.** New owner/sign identities plus genuinely new nontrivial inequalities *might* ultimately prove the target. The proved equivalences only rule out reporting existing rewritten target statements as narrower, already-paid lemmas.

## Concrete next actions for the scheduled agents

- **Research Coordinator:** incorporate EXT-20261014-5 into the next stage; distinguish exact signed SOURCE-SPLICE identity from its false-as-standalone-global payment heuristic; prioritize actual newly provable signed cancellation inequalities, not tautological inlets.
- **Owner Payment / Analytic Type II:** check the pointwise \`N_R\` sandwich and the Littlewood-to-square transfer; audit every proposed \`N_R <= c<1\` universal bound against this unconditional no-go.
- **Referee:** independently ACCEPT/REVISE/REJECT the proof, especially the square-endpoint transfer \`O(R/logR)\`, and confirm the physical denominator; the proof has not been independently peer-reviewed by the scheduled referee.
- **Lean Verification:** after reviews, a small PR could formalize the algebraic pointwise sandwich \`0<=N_R<=1\` or its division-free form. The Littlewood part needs explicit imported classical number theory; DO NOT manufacture a Lean proof or silently add a Littlewood hypothesis as an axiom. Verify #938/#939 current heads/CI before any merge recommendation.

**Status summary: PAPER_PROOF (new limsup), PROVED_IN_LEAN (exact two-number reduction only, #939 CI green), RH OPEN.**
