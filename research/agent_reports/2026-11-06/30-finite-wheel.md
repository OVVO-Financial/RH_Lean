# RH | Finite Wheel & Incidence - 2026-11-06

## Early CORR4 Checkpoint - 20261106-wheel-1

**PARTIAL / IN_PROGRESS. No new theorem is asserted at this checkpoint.**

Actual invocation: SCHEDULED, 2026-11-06T02:05:01-05:00, America/New_York; RUN_ID_UNAVAILABLE. Authority verified at main **4a6e6b8c1a81f6dd8b8bc0cfad123bbc2a56188a**, tree **48b193cd105e21183b1cfd68b059894c8056f35c**. AGENTS blob **547dda0d9456e7a4e1165dc72d59da6f70d5c023**; proof-contract blob **7c4ac83a1ec1a4144e1bd691391ed4244f1cc27c**; current routing policy **ffd8f1c65cc4da656174956d4e03b48bea46768b**.

deployment_ack: NO_PIGEONHOLING_ROUTE_SELECTOR_V1. Selected route **CORR4**, following the actual November 5 CORR4 / FINITE-AC / MU-LIFT rotation. No other agent is launched. The next distinct protected route is FINITE-AC.

### Structural Question

Resume Wheel 20261105-wheel-1/F1-F4, Census 20261105-census-1's joint R=57/58 caps, and Coordinator C53-C56. Fixed-label per-root relaxation countermodels already survive every sub-square-root prime rule and a sublinear whole-prefix envelope. Do not rerun or relabel that construction.

Investigate instead the common sequence across roots. For genuine Mertens prefixes,

```text
X_R=R^2-1; S_R={odd prime q:q^2<R};
m_R=M(R-1); G_R=M(X_R)-m_R; d_q(R)=M(floor(X_R/q^2));
H_R=sum_(R<=n<=X_R)mu(n)^2
    +2 sum_(q in S_R) q^(-1)sum_(R<=n<=floor(X_R/q^2))mu(n)^2;
B_R=G_R^2-H_R+sum_(q in S_R)(2G_R*d_q(R)/q-2d_q(R)^2).
```

Test whether the exact square dilation and its occurrence multiplicities force a nontrivial WEIGHTED CROSS-ROOT cap defect, or a coercive comparison for the entire B_R. Preserve the historical prefix, strict moving q^2<R mask, all daughters, all mixed terms, and finite lower/upper boundaries. An integrated comparison is not a pointwise estimate or a new endpoint bound.

Preregistered development: exact source reconstruction at R=56..128, held-out 129..256 and 317/1027; strict activation R=q^2 and q^2+1; integer dilation equalities on q-multiple roots; exact rational finite weighted tests at exponents with rational antiderivatives. Genuine Mobius and explicitly synthetic coherent controls remain distinct. No unchanged large wheel scan or exponent fit.

### Continuity And Formal State

Reports pinned at **aa215fa54489b8662a551dfe0296ba33b14b66c5**. Today Owner and Analytic are available. Coordinator, Census, Referee and Lean: **TODAY=PENDING / YESTERDAY=CARRY_FORWARD**. Yesterday's own three invocations were retrieved. External inbox blob **038018145c0fddb2f6306c0712373adf9cd1ea52** has no entry after October 18; its scope safeguards persist, its old routing/cadence does not.

Today Owner BT1-BT2 reclassifies old OPEN-SAT-I at paper scope using inherited input; RZ1-RZ3 retain the genuine floor response. Today Analytic FP1-FP5 preserves the constant parent and prime-square birth under frequency averaging. Neither is a new CORR4 signed supplier. These new claims remain independently review-pending.

PR #1096 is now human-merged at current main; open/draft collection is empty. The exact finite cancellation source was retrieved (blob **3cbc5159536d6b9e5000f74c5bd018bd2d62daf1**). Previous exact-head CI/axiom evidence is carried forward until directly checked; its finite theorem is not a new summatory estimate.

### Pending Work

Proof, falsification, novelty search, complete return, precise missing inequality, source/evidence ledger and final resume capsule are PENDING. eta_gate **SEARCH_BROAD**; net new endpoint gain **UNKNOWN**. The canonical VF von-Koch objective and RH remain OPEN.
