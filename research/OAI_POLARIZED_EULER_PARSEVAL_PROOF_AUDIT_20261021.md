# #997: actual mixed NNS rows, phase-correct Euler parity and Parseval scope

2026-10-21. Status: EXACT finite algebra, under targeted Lean verification. No new unconditional moment exponent or zero-free half-plane is asserted.

## Actual source and correct degree

The source is OpenAI's DetectorPlainMarkedFineField.lean, theorem source_batch_plain_marked_fine.

Its integrand over the ORIGINAL character-row family F.rows is

    |W(u)|^2 |P_j(u)|^2 |P_k(u)|^2,       j+k<=2,

where W(u)=F.physicalProduct selected u is the ORIGINAL masked physical product.

For each ideal-labelled polynomial P_h(u)=sum_a b_{u,h,a}, set

    K_h = sum_a |b_a|^2,
    P_h = sum_{a<b} max(Re(b_a conj(b_b)),0),
    N_h = sum_{a<b} max(-Re(b_a conj(b_b)),0).

The invertible complex-to-real map Phi already compiled in STABLE_FAR_PERRON_REALIFICATION gives the real Gram kernel (Phi(a) dot Phi(b))/2. Its products separate exactly into eight unnormalized signed NNS quadrants.

The correct degree-four POLARIZATION is:

    |P_j|^2 |P_k|^2
      = K_j*K_k
       +2*(K_j*P_k+K_k*P_j)
       -2*(K_j*N_k+K_k*N_j)
       +4*(P_j-N_j)*(P_k-N_k).

For j=k=0, this becomes K^2+4KP-4KN+4(P-N)^2.
For different j,k, the last mixed residual may have EITHER SIGN.
Never take an extra fourth power of P_j P_k W; that would change the degree.

The NEW Lean module VF_919_OAI_POLARIZED_SIGNED_NNS_EULER_20261021.lean proves the scalar and original Finset-weighted identities, signed quadrant identity, phase-correct toggling, and degree 1/2 log-weight identities. A separate source-admission argument is required to identify the literal OAI ideal-polynomial atom arrays with these abstract functions.

## Parseval: genuine obstruction, carefully scoped

For a complete uniformly weighted orthogonal family of characters that distinguishes the relevant ideals:

    average_chi |sum_a c_a chi(a)|^2 = sum_a |c_a|^2 = K

and Jensen gives average fourth moment >= K^2.

The exact four-point expansion partitions equal-ideal products a*g=b*d and unequal ones:

    M4 = Wtot * sum_m |sum_{a*g=m} c_a*c_g|^2
         + nonresonant_term,

provided that characters take unit values on the admitted ideals and that c_a is fixed (not secretly dependent on chi). Distinct ideals can still be resonant in the relevant ray-class quotient. Mark these equivalence classes correctly.

IMPORTANT: the first term is NOT a lower bound for the complete moment on arbitrary weighted or restricted F.rows. The nonresonant contribution may be negative. Explicit finite counterexample: coefficients (1,-1) on ideals 1,p and detector containing only the trivial character. Total fourth moment is 0; equal-ideal resonant convolution has coefficients (1,-2,1) and squared norm 6. The nonresonant term cancels the resonant term.

Thus the strong post-character H3 near-zero-row obstruction is rigorous for a complete orthogonal family, but cannot be stated unchanged for masked / weighted detector rows.

## Correct phase-preserving Euler toggle

For coprime new ideal-prime p and paired factor sets T,T+p:

    a_T - chi_u(p)*a_(T+p)
     = (a_T-a_(T+p)) + (1-chi_u(p))*a_(T+p).

The second term does NOT vanish because arithmetic weights coincide. A character value -1 with both weights 1 makes the residual 2, not 0. If a_T itself depends on the character row u, then it is not a common pre-character coefficient vector. Either extract row dependence into the fixed transform and prove its operator bound, or estimate the actual row-dependent masked source.

For verified log-polynomial derivative coefficients, let x=log N(T), L=log N(p), b=chi_u(p)*a_(T+p):

    j=0: a_T-b
    j=1: a_T*x-b*(x+L) = (a_T-b)*x-b*L
    j=2: a_T*x^2-b*(x+L)^2
           = (a_T-b)*x^2-b*(2*x*L+L^2).

The actual OAI polynomial / logProfile source must be checked to satisfy the assumed coefficient model, including annular cutoffs, before using these as its literal j-derivatives.

Smoothness alone does NOT yield a power saving from shifting N(T) to N(p)*N(T). For a profile smooth in log(N)/log U the mean-value cost includes |log N(p)|/log U; if N(p)=U^s (s fixed), this is O(s), not O(U^(-eta)). For sharp dyadic support a whole subinterval may be admitted on one side and excluded on the other, not a negligible boundary collar.

## Actual independent quantitative theorem still needed

Uniformly over the genuine conductor, row masks, selected slots, derivative indices j+k<=2, heights, and admissible ideal labels, prove ONE of:

(A) A **phase-correct, weight-preserving source contraction** after justified Euler toggling:
    ||a_comp||_2^2 <= U^(-eta) ||a_ref||_2^2
    with fixed eta>0, together with a real applicable operator fourth-moment bound for the SAME coefficient type and source. Row-dependent coefficients cannot be silently treated as fixed.

(B) A **resonant / nonresonant four-point character-kernel saving** for the SAME full marked source, paying all resonances, conductor collisions, absent partners, phase-dependent masks, and log-profile leaks.

An appropriate operator estimate of the form sum_u w_u |T_U(a)_u|^4 <= C*U^Gamma*||a||_2^4 would turn (A) into a U^(-2eta) gain. This is CONDITIONAL until both operator and source estimates are established for the actual Hecke data. The known OpenAI moment theorem alone cannot be used to infer (A) backwards.

The improved bound must be strictly below the binding moment exponent after all weights and parameter losses and must survive coupling to the inverse-second and unmarked ordinary moments to improve the Dirichlet half-plane.

## Corrected slack audit

The ACTUAL DetectorPlainMarkedFineField proof has

    state.width = 1 + D.t/4,
    stageError = D.t/4,

so the pre-relaxation exponent is 1+D.t/2; its exported bound is 1+D.t. A separate purported '5/6 -> 1' saving was NOT found at this theorem and must not be advertised as another fixed 1/6 gain. Moreover D.t/2 may vanish with the zero-free parameter and may not be globally binding.

## Acceptance

- Committed new NNS/Euler algebra: under targeted warning-fatal Lean 4.34.1 check on #997.
- Original #997 marked quartic: previous CI failed three tactics; one raw-width proof repaired and re-check required.
- Finite 317/1027 genuine sextic ideal phase witness: numerically validated, not an asymptotic uniform moment estimate.
- Unconditional source contraction / four-point saving: OPEN.
- New quasi-RH bound: not claimed.

Bottleneck: independently prove a fixed-power bound on the PHASE-CORRECTED, MASKED and DERIVATIVE-WEIGHTED Euler-compensated coefficient source (or full four-point Hecke character kernel), before applying a positive fourth-moment norm.
