# Independent mathematical audit: proposed \(\mathcal I_K^{(6)}\) lift of OpenAI's \(7/8\) proof

**2026-10-19 • Draft PR #984 • RH_Lean-original arithmetic; NO OpenAI theorem imported.**

The **central architecture is correct**: retain complete ideal labels \((\mathfrak a,\mathfrak p,\chi_{\mathfrak p},u)\), physical source masks, actual Möbius signs and all cross terms through spectral estimates. Project to rational owner weights **only after** preserving the full Hermitian sum.

The provided candidate derivation does **not** yet prove \(7/8\), because several specific asserted intermediate statements either are false or require stronger hypotheses than supplied. The corrections below are mathematically checkable and essential to an independent Lean proof.

## A. What can be proved at the exact algebraic level

1. **Primary generators:** O=Z[\(\omega\)], \(\omega^2+\omega+1=0\), is Euclidean. On ideals coprime to (3), \((O/(3))^\times\) has six elements and the reduction \(\mu_6\to(O/(3))^\times\) is an isomorphism. Thus the unique generator \(\alpha=a+b\omega\) with \(a\equiv1\pmod 3,b\equiv0\pmod3\) is multiplicative. Do **NOT** add \(\Re(\alpha)>0\): the genuine primary generator \(-2-3\omega\) has norm \(7\) but real part \(-1/2\). Reduction modulo \(1-\omega\) kills the cubic units \(\omega^j\), so it does NOT distinguish them.
2. **Deleted prime fibers:** the ideal monoid \(\mathcal I_K^{(6)}\) explicitly removes primes of norm divisible by 2 or 3. The claimed full prime-power fiber identification includes inert 2 and ramified 3. One must first establish the complete norm-fiber function on **all nonzero ideals**, then apply the native deletion/restoration operators for 2 and 3 (\`vf919ExcludedNorm_restored_character_eq_mobius\`), or work exclusively with the coprime-to-six coefficients on both sides.
3. **Rational Möbius is NOT the raw ideal fiber coefficient.** At the split-semiprime owner \(133=7\cdot19\), \(a_K(133)=4\), but \(\mu_{\mathbb Z}(133)=+1\). The exact \(\chi_{-3}\) convolution reads \(4-2-2+1=1\), and the same local pattern holds at \(259,100531,1054741\). The full quadratic convolution must remain in the source, before the final projection. The four native sextic phase witnesses \(\chi_{\mathfrak p_p}(\alpha_k)\) are a **cross-evaluation** of a high prime ideal and a low generator; they do not, without a reciprocity/ideal-index theorem, equal \(\chi_{\mathfrak a}(u)\) for every ideal of norm \(pk\).
4. **Finite ideal-label Fubini and full Gram:** the new \`VF_919_NATIVE_IDEAL_FIBER_FUBINI_GRAM_20261019.lean\` proves for arbitrary finite ideal label set \(S\), owner \(N_i\), coefficient \(c_i\) and physical weight \(w\):
   \[
   \sum_{i\in S}c_iw(N_i)
    =\sum_{n\in N(S)}w(n)\sum_{i\in S,\;N_i=n}c_i,\quad
   \left|\sum_{i\in S}c_iw(N_i)\right|^2
    =\sum_{i,j\in S}\Re(c_i\overline{c_j}w(N_i)\overline{w(N_j)}).
   \]
   Distinct same-norm ideals are OFF-DIAGONAL in ideal labels but remain included in the full sum. This algebra alone imposes no cancellation or power saving.

## B. Specific false / unproved analytic inferences

| Proposed step | Claim | Correction |
|---|---|---|
| 9 | Defining \(\widehat{\mathcal T}=\widehat K_\theta/\widehat K_\mathrm{native}\) **transfers all analytic estimates** | A quotient on a nonvanishing strip need not define an \(L^1\)-bounded Mellin convolution (zeros, poles, growth and uniform inversions require proof). Even a bounded convolution on the scale variable CANNOT change the underlying \(c n^3\) arithmetic or manufacture ideal labels. The two *source coefficient measures*, not just scalar kernels, need an independently proved identity. |
| 13 | Theta reflection directly gives \(O_A((1+|s|)^{-A}q^{-A})\) uniformly in the conductor \(q\) | Poisson reflection includes conductor normalization and dual-frequency zero/main terms. Exponential decay in a dual variable does not automatically imply arbitrary conductor power saving. The proposed displayed factor \(\exp(-c N(\alpha)/x)\) has no \(q^{-A}\) consequence. |
| 14 | Multiplicativity of sextic residues automatically yields \(|\tau_6(\chi_\mathfrak a,1)|=\sqrt{N\mathfrak a}\) | Gauss normalization requires **primitive, nontrivial** characters and the exact nondegenerate additive character for the actual conductor. For imprimitive/ramified rows, zero extensions and conductor changes matter. Multiplicativity by itself is insufficient. |
| 15 | Replace \(\zeta\) in \`growthExponent_eq_rightmost\` with a finite product of Hecke L-functions to obtain uniform Hecke-family zero-supremum equivalence | A fixed finite product cannot control the SUPREMUM over arbitrarily moving moduli. Uniform constants, holomorphic continuation and family zero-detector must be built; no such replacement is automatic. |
| 16 | For EVERY pair \(\mathfrak a\ne\mathfrak b\), the ratio character is nonprincipal and its off-diagonal \(u\)-sum cancels | Distinct ideals do not supply a kernel-checked globally primitive ratio statement with all masks. Even a truly nonprincipal character has zero SUM only over appropriate COMPLETE residue classes; incomplete dyadic sums need genuine character-sum estimates. On sixth-power rows \(u=v^6\), every nonzero sextic character evaluates to \(1\), so off-diagonal phases can align rather than cancel. |
| 16 | Per-pair \(D^{1+\epsilon}\), \(O(D^2)\) pairs is a useful power saving | Their own triangle estimate yields \(O(D^{3+\epsilon})\), or \(O(D^{2+\epsilon})\) after \(D^{-1}\) normalization: only the baseline, not the required refined bound. |
| 18/20 | Inserting a generic dilation \(T_{\mathfrak p}W\) identifies OpenAI's **marked-minus-rescaled theta source** with RH_Lean's actual \(S=A-T\) | Both include two terms but are not the same operator: original sharp/root-clipped weights, changed prime-ideal scale, normalization, and source-incidence masks differ. An occurrence-preserving equality must be proved prior to analytic transfer. |
| 22 | OpenAI's compensated local remainder is universally \(E_{\mathfrak p}-1=-\chi_{\mathfrak p}(u)^2N\mathfrak p^{-2s}\) | This is NOT what \`nativeLocalCompensation_equation_5_13b\` says. Its right side includes both \((U-Q_w)(V/(1-V)-D)\) AND \((A+U-Q_w)E\), with actual \(P^*\), normalization, and denominators. No substitution in the proposal has proved either term equals the posited pure quadratic. Consequently the \(N\mathfrak p^{-2\sigma}\) majorant is presently unestablished for the genuine local source. |
| 28 | The product of those hypothetical quadratic remainders is the actual nonzero principal normalizer | A product of toy factors \(1-z_p^2\) may be nonvanishing for \(\Re s>1/2\); this does not identify the actual *signed* principal normalizer \(B_p=-1+O(Np^{-7/8})\) and its analytic correction. Otherwise the critical high-row analytic work would disappear without justification. |
| 30/34 | Only \(\sum|\alpha_{\mathfrak a}|^{6/5}\ll D^{1+c}\) plus Hölder forces \(\sum_u|\mathcal M_u(D)|^2\ll U+U^{1/6}D^{5/6}\) | **FALSE with that hypothesis alone.** At principal row \(u=1\), take \(\alpha_{\mathfrak a}=1\), smooth nonnegative \(W\) with \(\asymp D\) supported ideal coefficients. The normalized row has square \(\asymp D\), while the asserted rhs is \(D^{5/6+\epsilon}\) for \(U=1\), \(\epsilon<1/6\). Need the FULL signed ideal-Möbius/marked amplification and Poisson estimate, including arithmetic admissibility, not abstract coefficient size. The Lean file \`VF_919_SEXTIC_ANALYTIC_BRIDGE_FALSIFIERS_20261019.lean\` formalizes the polynomial obstruction. |
| 31/32 | A Stage-I baseline automatically yields the refined fourth and unmarked second moments | Raising a prime polynomial to fourth power produces additional diagonal and secondary principal coincidences, ramified masks, and conductor constraints. The naive Stage-I pair bound does not have the refined uniformity claimed. |
| 35 | \(k!\ll_k1\) supplies the required uniform slot-count saving | It is only a bound for each FIXED k. If induction allows k to grow with \(\log D\), constants must be controlled quantitatively; \(k!\) can consume the desired power margin. |
| 36/37 | \(U^{1/6}D^{5/6}\le U\) for \(D\le U^{6/5}\) | **FALSE:** the threshold is exactly \(D\le U\). For \(U=32,D=64=U^{6/5}\), raising to the sixth power gives \(32\cdot64^5>32^6\) (Lean checker). Including the extra source \(D^{5c/6}\) makes the condition \(D\le U^{1/(1+c)}\), more restrictive. The false inequality breaks the proposed low/high band covering. |
| 38 | Insert a Hecke moment bound into \`covarianceUpperBounded_iff_energyUpperBounded\` to get rational Möbius decay | That theorem is an **identity/equivalence about rational Mertens weighted covariance**. It is not a theorem transferring an arbitrary Hecke \(L^2\) moment into that covariance. Moreover controlling its energy for *every* \(\epsilon>0\) is RH-scale; a \(7/8\) Mertens input typically only gives energy convergence for \(\epsilon>3/8\). The needed norm-fiber + signed quadratic convolution transfer is missing. |
| 39/40 | A zero at \(\beta>7/8\) automatically forces lower moment \(U D^{2\beta-1}\), hence final contradiction | This is the **zero-detector theorem**, not a consequence of a finite phase table. OpenAI proves a common meromorphic/holomorphic probe, principal signal, contour reflection and positive lower obstruction, with uniform \(u,D,t,\mathfrak q\). Each is a substantive analytic assertion on the SAME source. |

## C. What the user's central idea DOES correctly identify

The right operator order is:

\[
\boxed{
\text{(full ideal index, sextic phase, primitive conductor, source masks)}
\xrightarrow{\text{TRUE analytic theta/Poisson}}
\text{(exact variable-conductor moments)}
\xrightarrow{\text{uniform power saving}}
\text{(complete character-row gram)}
\xrightarrow{\text{norm fiber + }\chi_{-3}\text{ convolution}}
\text{(genuine rational signed owner source)}.
}
\]

The mathematical acceptance is that EVERY arrow is a **proved equality or quantitative bound**, with valid exponent/normalizer/scale hypotheses, ultimately yielding a genuine native unconditional theorem \`∀ s : ℂ, (7/8 : ℝ)<s.re → riemannZeta s≠0\`. The crosswalk already locates dozens of exact identities. The proposed new finite fiber Fubini/Gram lemma confirms the norm projection is not itself the problem: **the unfounded extra power saving in the middle is the problem**.

Do not silently upgrade a source-independent Gram identity to an arithmetic large-sieve bound, or a \`Prop\` stating a needed moment to a kernel-checked proof. Nor should the absence of the analytic bound be relabeled a computational artifact. A complete independent RHLean proof is still open after this audit.
