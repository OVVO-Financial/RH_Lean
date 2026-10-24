# Co–Div rate: from an original one-prime estimate to the full Gaussian high row

**Date:** 2026-10-22. **Status:** finite arithmetic and source-local theorem proposed in Lean; mixed-OAI/native CI pending; full original-source transport and character moments OPEN. PR #1005, stacked PR #1006. Pinned source: openai/math 1581d4cbdd69a0faf34b2089614fe2a814316a6a.

## 1. Exact currency; not an independently proved rate

For the original weighted physical source F_u, the native NNS identity is

\[
E=\sum_u\omega_u |F_u|^2
  =D_{\rm diag}+C_{\rm off}-V_{\rm off},\qquad\omega_u\ge0.
\]

For \(T=Z^{2(\beta-11/16-\sigma)}\sum_u\omega_u B_u^2\),

\[
E\le T
\iff C_{\rm off}-V_{\rm off}\le T-D_{\rm diag}.
\]

This is an equivalence, NOT an independent proof of the bound on the right. In particular, complete-orbit sextic orthogonality or positive semidefiniteness does not yield a source-specific negative offdiagonal payment.

## 2. Correct the physical central contour

Original PrimeRows/CentralSlots.lean requires

\[
\Re x=a+16e,\quad \Re w=1-a-6e,\quad\Re z=17/50.
\]

The former \(\Re w\ge1/2\) premise in PR #1005's VF919OriginalOnePrimePowerGain.lean excluded the physical \(a=7/8\) line. The corrected local source proof needs only \(\Re w\ge0\). The added theorem oai_one_prime_physical_central_contour_power_gain uses

\[
7/8\le a,\qquad a+6e\le1,\qquad e\ge0
\]

and concludes

\[
|\operatorname{unramifiedSelected}
+\operatorname{unramifiedClosed}\overline v|
\le720 Q^{-7/8}.
\]

The actual marked profile Pstar, prime-dependent D, growing B and Q=N(Pideal) are preserved. For example, the formerly problematic BKV product satisfies \(Q^{1-\Re w-6\Re z}\le Q^{-1.04}\le Q^{-7/8}\). No claim is made for the physical subrange a+6e>1, where \(\Re w<0\) and the existing hW<=1 argument no longer applies. Warning-fatal mixed OAI CI must accept the new theorem.

## 3. Genuine exponent on a ONE-PRIME dyadic band

Let S be DISTINCT selected Eisenstein prime ideals of norms in [P,2P), with P>=4, N=|S|<=CP, and suppose the actual compensated combined local residue obeys \(|b_p|\le720P^{-7/8}\). Then

\[
\|b\|_{\ell^{6/5}(S)}
\le720P^{-7/8}N^{5/6}
\le720C^{5/6}P^{-1/24}.
\]

The native theorem oai_one_prime_dyadic_l65_power_rate in PR #1006 proves this *finite scalar implication*; its Lean CI is pending. The exponent is strictly positive because \(7/8-5/6=1/24\). The local complex bills are recombined BEFORE absolute value and then the 6/5 norm is taken.

Distinct prime ideals of Eisenstein integers obey a crude elementary linear count: for each rational prime below 2P there are at most two prime ideals, so N<=4P. This is not a bound on the number of marked-prime/cofactor OCCURRENCES in the complete original source, and the count has not yet been source-instantiated in the native lemma.

For nonnegative physical row weights \(\omega\) of total \(\Omega\) and phases of modulus <=1, the one-prime DIAGONAL, with the same local bound and slot count, satisfies

\[
D_{\rm one-prime}
\le 720^2\,C P^{-3/4}\,\Omega,
\]

by \(N P^{-7/4}\le CP^{-3/4}\). This is a direct paper argument, not yet a typed theorem for the complete source.

## 4. Strict obstruction to assuming a Co–Div silver bullet

Take N approximately P perfectly phase-aligned scalar atoms, each \(b_p=720P^{-7/8}\), on one row. Then

\[
E=\left|\sum_p b_p\right|^2\asymp P^{1/4},\qquad
D=\sum_p|b_p|^2\asymp P^{-3/4}.
\]

So pointwise prime decay and linear count DO NOT control the full energy. The coherent offdiagonal term can cost a factor P. Conversely complete orthogonal phase rows give E=D without any negative net Co–Div offdiagonal payment: a SMALL DIAGONAL plus a CONTROLLED signed offdiagonal is sufficient.

With the trivial sixth norm of N unit phases, Holder gives only
\(\left|\sum_p b_p\psi_p(u)\right|\lesssim P^{-1/24}P^{1/6}=P^{1/8}\).
The missing gain must be a physical source-specific incomplete Hecke phase estimate or additional cancellation of grouped coefficients; it cannot be extracted from finite Holder alone.

## 5. Source-specific closure targets

1. Prove physical ideal/row admission of the new one-prime bound using ORIGINAL continuedCompensatedLocal_unramified, supported good prime, true conductor coprimality, original row mask, original phase norms, and original contour; handle the negative-w region separately.
2. Prove normalization and all-admitted effective-ideal coefficient factorization. Marked/cofactor multiplicities require an independent convex ell-6/5 bound. For tau=1 unique ideal factorization supplies only ONE decomposition, so no inter-decomposition cancellation.
3. Prove the actual incomplete-Hecke sixth-root operator bound for ALL row tests, true omega, masks, and conductor geometry; an unweighted complete sextic orbit does not suffice.
4. Pay the actual principal normalized inverse-Mellin residue, the row-constant complex normer, and principal/nonprincipal cross via \((\sqrt{E_R}+\sqrt{E_H})^2\).
5. With separately established bounds, prove \(E\le T\) on ORIGINAL full Gaussian/Mellin source. Do not use the target \(C_{\rm off}-V_{\rm off}\le T-D\), hHigh, SourceMomentsAt or equivalent high-row bound as a premise.

**Conclusion:** Quantitative Co–Div may be decisive when source-derived, but it is not free from NNS reassembly. The true one-prime P^(-1/24) is a concrete rate step, not a proof of the complete high-row estimate, 7/8 replication, or RH.
