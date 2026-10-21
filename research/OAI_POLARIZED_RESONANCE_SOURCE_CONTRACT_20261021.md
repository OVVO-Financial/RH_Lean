# #997: Polarized NNS, exact resonant floor, and twisted Euler source

Date: 2026-10-21. Status: **unconditional finite algebra plus explicitly conditional analytic contract**. This file audits the proposed resonance / source-energy argument against the actual [OpenAI marked-moment theorem](https://github.com/openai/math/blob/main/lean/OAI/NumberTheory/DirichletL/Detector/DetectorPlainMarkedFineField.lean). It does not claim an improved zero-free exponent.

Native finite Lean: [VF_919_OAI_POLARIZED_SIGNED_NNS_EULER_20261021.lean](VF_919_OAI_POLARIZED_SIGNED_NNS_EULER_20261021.lean).

## A. The correct marked source and the polarized real NNS identity

OpenAI bounds, over the **actual** fibre F.rows, every j,k >=0 with j+k<=2:

    M_jk = sum_{u in F.rows} |F.physicalProduct selected u|² *
             |P_j(u)|² * |P_k(u)|²
         <= C*(1+height)^J * U^(1+D.t),   U=Z^d.

The original P_j uses OAI's logProfile^[j] positiveAnnular and its genuine family, masks, heights and selected slots. It is not a generic polynomial of log norm without a further dictionary theorem.

For an *admissible source expansion* P_j(u)=sum_{alpha in I_{u,j}} a_{u,j,alpha}, define each ORIGINAL ideal-pair real Gram via Phi(z)=(Re z-Im z, Re z+Im z):

    g_{alpha,beta} = [Phi(a_alpha)_1 Phi(a_beta)_1 +
                       Phi(a_alpha)_2 Phi(a_beta)_2]/2
                   = Re(a_alpha * conjugate(a_beta)).

Each Phi-coordinate product has four sign quadrants; the pair Gram has eight. Define

    K_{u,j} = sum_alpha |a_{u,j,alpha}|²,
    P_{u,j} = sum_{alpha<beta} (g_{alpha,beta})_+,
    N_{u,j} = sum_{alpha<beta} (-g_{alpha,beta})_+,
    E_{u,j} = K_{u,j} + 2(P_{u,j}-N_{u,j}) = |P_j(u)|².

These are unnormalized original source sums, BEFORE a norm or a stripped-owner projection.

For mixed j,k, the correct **degree-four** identity is

    E_j E_k =
      K_j K_k
      + 2(K_j P_k + K_k P_j)
      - 2(K_j N_k + K_k N_j)
      + 4(P_j-N_j)(P_k-N_k).                       (P1)

The last term can be NEGATIVE for different derivative rows; it is NOT universally a positive residual. For j=k=0 it is +4(P-N)²>=0, giving the pure fourth identity. Applying the pure fourth identity to P_j P_k W instead would raise the degree and depart from OAI's actual theorem.

The existing #997 Lean module proves the conditional row identity, exact unnormalized varying-weight finite fibre sum, the negative-payment implication, Phi sign quadrants, and the phase-twisted Euler pairing. See also [the 317/1027 and Parseval numerical regression](../scripts/oai_marked_polarized_source_audit.py). **It does not yet prove the exact expansion of OAI's actual P_j(u) as its own annotated ideal atom list.** That is an independent type-correct source-lift obligation.

## B. Resonant four-point character floor: valid exact statement and essential caveat

For a FIXED, character-independent coefficient array a over a finite set of distinct ideal labels, characters unit-valued on admissible ideals, define F_chi=sum_alpha a_alpha chi(alpha). The pure fourth-moment expansion is

    sum_chi w_chi |F_chi|⁴ =
      Wtot * ||a*a||_2² + NONRESONANT,

where Wtot=sum_chi w_chi and a*a(m)=sum_{alpha gamma=m} a_alpha a_gamma.
The expression labelled RESONANT is exact for alpha gamma=beta delta as *ideals*, where chi(alpha gamma)conj(chi(beta delta))=1. **More coincidences may occur modulo the conductor** (two different ideals may have the same character value), and if chi vanishes at inadmissible ideals the unit statement fails; restrict to actual nonvanishing character labels.

Critical correction: the resonant expression is NOT in general a floor for the FULL moment with incomplete/nonuniform character weights: NONRESONANT may be negative. Example for the group of order 2 with a=(1,-1): the trivial character gives F=0, so a sample consisting solely of the trivial character has fourth moment 0 despite a positive formal multiplicative-diagonal term. Over the COMPLETE uniform character family, Parseval kills the off-diagonal modulo the character kernel, and the fourth-moment floor becomes a genuine inequality.

For the FULL uniform dual of a finite abelian group, AFTER the original ideals
have been aggregated by their actual character-class map, define
b(g)=sum_{alpha: class(alpha)=g} a_alpha. Then:

    E_chi |F_chi|² = ||b||_2², and
    E_chi |F_chi|⁴ >= (E_chi |F_chi|²)² = ||b||_2⁴.

Equivalently the FULL normalized fourth moment equals ||b*b||_2², at least ||b||_2⁴. If the ideal-to-class map is injective on the actual source support then b and a have the same ℓ² norm and this reduces to the originally proposed ||a||_2 floor. Otherwise opposite source coefficients on distinct ideals with identical class signatures can cancel **before character averaging**, giving ||b|| much smaller than ||a||. The raw ideal-indexed resonant diagonal is therefore not an all-character lower bound without this alias control. This is the rigorous Parseval/Jensen obstruction to claiming near-total cancellation on almost every UNWEIGHTED character for fixed source coefficients.

**Mixed derivatives differ:** a_j*a_k can cancel, and no general inequality ||a_j*a_k||_2² >= ||a_j||_2²||a_k||_2² holds; do not transfer the pure-row floor unmodified to j!=k.

OpenAI's F.rows are conductor/height/slot restricted, and its physicalProduct can depend on row u. Thus neither the complete-dual orthogonality nor a fixed source coefficient array can be assumed. An independent character large-sieve / four-point kernel estimate must establish the correct restricted analogue.

## C. The character-twisted Euler pairing that survives the source

For each legal subset T not containing selected prime ideal p, its toggled partner is T union {p}. In a true row character expression the selected prime changes both its weight AND its phase:

    a_pair(u,T) = (-1)^|T| chi_u(product T) *
                    [W_u(T) - chi_u(p)*W_u(T union {p})].      (E1)

For phase=chi_u(p), the complete elementary identity is

    W0 - phase W1 = (W0 - W1) + (1-phase)*W1.         (E2)

It is implemented in Lean as twistedEulerPair. If W0=W1=W and phase=-1, then residual=2W, NOT 0. **No scalar smoothness estimate can suppress the character-phase term automatically.** True pre-character l2 shrinkage requires a compensated ideal coefficient a_comp INDEPENDENT of u or a proven phase-lift carrying the ideal labels correctly.

A further geometric caution: if the SAME smooth cutoff is supported only on [U,2U], and N(p)>=2, then both N(T) and N(p)N(T) are in [U,2U] only at the possible shared boundary N(p)=2, N(T)=U. There is no nonempty interior on which both factors are automatically in that SAME dyadic window. Different windows/annular smoothing may create overlap, but must be inspected at OAI's actual profile scale. The informal claim "smooth weight changes only near the boundary collar" is false without such a scale relation.

## D. Derivative weights: j=0,1,2 discrete Leibniz, with an OAI-profile caveat

For a literal logarithm l=log N(T), b=log N(p):

    (l+b)^0 - l^0 = 0;
    (l+b)^1 - l = b;
    (l+b)^2 - l² = 2lb+b².

Lean lemmas phase_correct_log_one and phase_correct_log_two prove the exact phase-weighted forms. For a source term a_T with derivative coefficient (log N T)^j, the paired logarithmic part is

    l^j W(T) - phase*(l+b)^j W(T union {p})
      = l^j[W(T)-phase W(T union {p})]
        -phase*[(l+b)^j-l^j]*W(T union {p}).

The second correction has degree j-1 in l and explicit b=log Np. But OAI's actual logProfile^[j] positiveAnnular may also act on a smooth annular profile, and this factor identity must be proved for its true row source; do not assume bare log moments without checking.

## E. The exact new quantitative bottleneck

To improve the detector, prove one of these **independent, unconditional and uniform** estimates for the actual marked ideal source and its parameter range:

1. **Pre-character source cancellation:** a compensation identity constructs a row-independent, fully phase/ideal-labelled a_comp with
      ||a_comp||_2² <= C U^(-eta) ||a_reference||_2²
   for eta>0, uniformly under all selected-slot, conductor, height and masking conditions. A separate actual fourth-moment operator inequality is then required to turn this into a U^(-2eta) fourth-moment saving. Merely writing down E1 or a character-dependent a_comp,u does NOT give this norm reduction.

2. **Four-point character contraction:** bound the restricted weighted C_U(alpha,beta,gamma,delta) kernel, including multiplicative resonances/modulus aliases and genuine row weights. An independent saving on the **binding** part of this kernel after source compensation could improve OAI's refined marked bound. No improvement follows from rearranging its already proved total fourth-moment estimate.

3. **Existing width slack:** the checked OpenAI source states state.width=1+D.t/4, stageError D=D.t/4, and then coarsens the resulting 1+D.t/2 to 1+D.t. This is the actual slack in DetectorPlainMarkedFineField.lean—not the claimed 5/6->1 at that location. Retain and compile this sharper bound upstream and test whether it improves the coupled detector budget after other moment inputs. This is separate from a newly proved arithmetic cancellation exponent.

PNT's M(x)=o(x), the squarefree Euler-product density and the finite even/odd subset pairing are valid but do NOT supply any of these restricted four-point / weighted-source estimates automatically.

## F. Acceptance and falsification

- [x] Prove the exact degree-four polarization and character-twisted coefficient algebra at generic finite-row level (Lean source candidate).
- [x] Validate P1, sixth-root finite signed NNS quadrants, incomplete-character counterexample, and the twisted prime toggle in deterministic finite code.
- [ ] Warning-fatal Lean 4.34.1 CI green on the new source.
- [ ] Establish the actual OAI P_j atom expansion and the physicalProduct slot masks without norm-only projection.
- [ ] Prove uniform source shrinkage or character four-point saving on the exact OAI restricted family.
- [ ] Establish a new unconditional all-Dirichlet zero-free exponent and pass the tracker canonical theorem; NONE is presently claimed.

This is an exact contraction target, not a relabeling of an assumed RH-strength moment bound.
