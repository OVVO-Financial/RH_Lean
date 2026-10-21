# PR #997: polarized NNS, Parseval resonance, and phase-correct Euler compensation

Date: 2026-10-21. Status: exact finite algebra and finite source tests only. This is NOT a new OAI analytic estimate, improvement to 7/8, or RH proof.

## The ACTUAL input, not a surrogate

The original OpenAI theorem source_batch_plain_marked_fine bounds the genuine selected-marked family, with rows F.rows, full derivative profiles and physical slot product:

    M_jk(U) = sum_u |W(u)|^2 |P_j(u)|^2 |P_k(u)|^2
             <= C (1+height)^J U^(1+D.t),  j+k<=2.

The two derivative rows P_j and P_k must be polarized SEPARATELY. Do not take the fourth power of P_j*P_k*W. For an admitted row and exact ideal atoms of each P_j, define:

    K_j=sum_alpha |a^(j)_alpha|^2,
    g^(j)_{alpha,beta}=Re(a^(j)_alpha conjugate(a^(j)_beta)),
    P^+_j=sum_{alpha<beta} max(g^(j)_{alpha,beta},0),
    P^-_j=sum_{alpha<beta} max(-g^(j)_{alpha,beta},0).

The sign split is taken on EACH ideal pair, before pooling. Fred Viole's invertible real Phi pair recovers g exactly, including all mixed quadrants. Thus E_j=|P_j|^2=K_j+2P^+_j-2P^-_j, and the exact degree-four identity is

    E_j E_k
      = K_j K_k
        +2(K_j P^+_k+K_k P^+_j)
        -2(K_j P^-_k+K_k P^-_j)
        +4(P^+_j-P^-_j)(P^+_k-P^-_k).

For j!=k the final mixed term has NO fixed sign. The new standalone Lean source VF_919_OAI_POLARIZED_EULER_BRIDGE_20261021.lean proves the scalar, arbitrary-row-weighted, and j=0,1,2 prime-toggle identities. The actual ideal-atoms-to-OAI-polynomial equality is a separate SOURCE-LIFT obligation, not silently assumed.

## Restricted resonance is not a moment lower bound

For a fixed ideal coefficient array a and a multiplicative character row chi_u, put b_m=sum_{alpha*gamma=m} a_alpha*a_gamma. Then

    Z_u=sum_alpha a_alpha chi_u(alpha),
    M4=sum_{m,n} b_m conjugate(b_n) C_U(m,n),
    C_U(m,n)=sum_u w_u chi_u(m) conjugate(chi_u(n)).

For coprime/nonzero unit phases, C_U(m,m)=sum_u w_u=Wtot. The diagonal RESONANT COMPONENT is Wtot*||a*a||_2^2, but M4_nonres need NOT be positive. This diagonal component is NOT a general lower bound for the restricted, weighted actual family.

Explicit group Z/2 counterexample: a(1)=1, a(g)=-1. The resonant component is 8. On ONLY the trivial character, Z=0 and M4=0, so the nonresonant contribution is -8. Averaging BOTH orthogonal characters gives M4=16=2*8. Complete-character Parseval is valid; applying it to an INCOMPLETE family without checking the off-diagonal kernel is not. In ray/class characters distinct ideals may remain character-indistinguishable, adding effective resonances. Non-coprime/zero character values require their own branch.

Actual OpenAI coefficients, source masks and external phases may DEPEND on u. Before factoring out a fixed a_alpha, that independence must be proved or the u-dependent amplitudes must remain INSIDE the four-point kernel.

## The exact Euler-prime phase and the derivative Leibniz bill

Let p be a fresh prime ideal and T a cofactor, with chi(Tp)=chi(T)*theta and theta=chi(p). For actual amplitude A:

    chi(T)*A(T)-chi(Tp)*A(Tp)
       =chi(T)*[A(T)-theta*A(Tp)].

The paired coefficient is A(T)-theta*A(Tp), NOT A(T)-A(Tp). Even/odd subset counts cancel exactly only when the CHARACTER-ALIGNED WEIGHTS match. The phase theta cannot disappear unless the source has an explicitly proved countertwist.

For a pure log-power model with L=log NT, ell=log Np, the three exact weighted toggles are:

    Delta_0=A(T)-theta*A(Tp)
    Delta_1=L*Delta_0-ell*theta*A(Tp)
    Delta_2=L^2*Delta_0-(2*L*ell+ell^2)*theta*A(Tp).

These are proven in Lean algebraically, but the actual OAI logProfile positiveAnnular polynomials must be IDENTIFIED with any claimed pure-log atom expansion before applying the equations to the production source. Do not assume the profile is simply (log Nalpha)^j without showing it.

## Dyadic smoothness alone does not save a power

A prime toggle changes the physical norm MULTIPLICATIVELY. With a hard [U,2U] window, n=1.5U lies inside while 2n=3U lies outside; this is not confined to a tiny collar near the window's endpoint. Even for smooth W,

    |A(T)-theta*A(Tp)|
       <= |1-theta|*|A(T)|+|A(T)-A(Tp)|.

The first phase term may be O(1). Smoothness of f(log NT/log U) controls only the second via (log Np)/(log U), not necessarily a fixed power; for Np=U^c it can remain order 1.

## Uniform sextic phases give another exact Parseval-type obstruction

For fixed source amplitudes a,b and all six equally weighted roots of unity theta^6=1,

    (1/6) sum_{theta^6=1} |a-theta*b|^2 = |a|^2+|b|^2.

Indeed, |theta|=1 and sum theta=0, so the cross term averages to zero. Therefore the naive phase-correct Euler pair DOES NOT lower averaged coefficient energy for a complete uniform sixth-root ensemble. A genuine source norm gain must exploit the actual unequal admissibility weights, a mathematically verified countertwist/compensator, or specific structure beyond complete character orthogonality. Those same changes must still pay the actual source masks and dyadic partner losses. This is a falsifier for unsupported source-energy contraction, not a refutation of OAI's existing valid compensated source machinery.

## The new analytic bottleneck

The unweighted Euler identity and PNT Möbius density do NOT imply weighted higher moments. Two possible SOURCE-FAITHFUL new theorems are:

(A) a true source-energy reduction on the actual coefficient array after physical marking and phase-aware pairing: ||a_comp||_2^2 <= C U^(-eta)||a_ref||_2^2, eta>0, together with an applicable bounded fourth-moment operator for that SAME array. If theta depends on the row, a_comp may also be row-dependent; a fixed source operator cannot be introduced without proof.

(B) a uniform four-point kernel contraction on the actual labelled source, with the C_U(m,n) off-diagonal, resonant/character-equivalent classes, zero character cases, height, conductor, and selected masks all paid. The final theorem must improve a BINDING OAI moment cost. Rewriting the same old marked bound in NNS cannot improve its exponent by itself.

The ACTUAL refined marked proof currently has state.width=1+D.t/4 and stageError=D.t/4, relaxing the unrounded sum 1+D.t/2 to 1+D.t. This is a separate quantitative tightening candidate and NOT the claimed 5/6 -> 1 step in that file. Any improvement must survive the complete three-input moment assembly and detector geometry.

## Evidence and status

Finite numerical tests in scripts/oai_marked_polarized_euler_audit.py verify all six j+k<=2 log-derivative cases on RH_Lean's 317/1027 ideal-phase lists; the pure fourth-moment totals are 16,1,1,1 (sum 19), retaining every original signed pair. They test both multiplicative phase-correct Leibniz identities and the incomplete-Parseval and dyadic partner-escape counterexamples.

Lean module uses only Mathlib and finite algebra, without sorry or any unproved analytic cancellation axiom. Its warning-fatal Lean 4.34.1 CI is the proof authority, not the math note. No new zero-free endpoint is claimed.
