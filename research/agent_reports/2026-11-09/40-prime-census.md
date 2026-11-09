# RH | Prime Census Laboratory - 2026-11-09

## Pre-Registered Cross-Root Test - 20261109-census-1

Execution: IN_PROGRESS. Mathematical status: PENDING. Scheduled trigger 2026-11-09 03:11:02 EST, America/New_York; platform RUN_ID_UNAVAILABLE. This is one actual invocation.

finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1.
Pinned main: 8110624150e444964f998676bf54e2e9a3b7e91c.
AGENTS blob: 6695522a45d67fd1e80a7cff1f98d909405036e2.
CURRENT_PROOF_CONTRACT blob: 95566e37c8eaeb99ee680660df4f9d2e06ea5038.
Finite-wheel directive blob: e505f35522b675c6b5b263eac73618d717346973.
Original complete-wheel Lean source blob: ecb482e52deeee5e9b3853592a3ffdace662d2ff.
Initial report snapshot: 136dad6b6c6c401bb5b60f2d59ca85eec5356eae.

The governing target remains ONE C>=0, before every integer R>=2, with |F_R-D_R|<=C R log R, where X=R^2-1, y=R-1, F_R=sum_(d|P_y)mu(d)fract(X/d), D_R=X delta(y)+pi(y)-1-li(X). The certified identity F_R-D_R=li(X)-pi(X) does not supply the missing bound. All virtual divisors remain until Euler compensation.

### Continuity And Changed Question

November 9 Owner FW1-FW6, Analytic SC1-SC6 and Wheel RA1-RA5 are available and their relevant derivations/handoffs have been read. Today's Coordinator, Referee, Lean and prior Census are PENDING; use their November 8 reports as YESTERDAY=CARRY_FORWARD. All seven November 8 latest summaries and the external inbox were retrieved. The inbox has no entry newer than October 18. Preserve old FM's non-Mobius scope, FR's different Mobius carrier, SG's unreviewed paper status, and EC's later merge in #1119. No open/draft PR at intake; recent accepted changes include #1123, #1118, #1121, #1122, #1120 and #1119. No local Lean or new CI is authorized or needed.

Do not repeat the leading owner-bias or root-admission scans. The new question is whether the proper cross-root quadratic error supplies deterministic negative compensation for its TWO linear responses, or whether the full product-boundary shape defeats marginal-sign heuristics.

### Frozen Carrier And Competing Predictions

For each integer R>=8 put A=[R/2,R), B=[R,2R], X=R^2-1, and Omega={(u,v) in A x B:uv<=X}. All lower prime atoms and pq=X are included, p=R excluded, q=R included. Write dnu=dpi-dt/log t and

N = integral_Omega dpi dpi,
C = integral_Omega dli dli,
U = integral_Omega dpi dli,
V = integral_Omega dli dpi,
L_A = U-C, L_B = V-C,
Q = N-U-V+C,
L = L_A+L_B,
N-C = L+Q.

These are proper terms of the original upper owner band, not the complete wheel. Define a0=nu(A), b0=nu(B), c0=a0*b0/2, retaining Analytic SC's constant frequency.

New laboratory hypotheses, NOT attributed to an upstream author:
H_CANCEL: Q*L<=0 for every R>=8; also measure the stronger |L+Q|<=|L|.
H_MODE: Q*c0>=0 for every R>=8.
Rivals: product-boundary shape allows reinforcement and/or reverses the marginal-mode sign. Strictly certified opposite inequalities reject the respective hypotheses; an unresolved interval is not a sign result.

Predeclared discovery range R=8..64; held-out range R=65..256; stress roots 257,317,549,1027,4096. Record smallest violations within the full stated domain, strongest observed margins and all sign changes. No fitted universal constant will be inferred. Track |F-D|/(R log R) only as a finite numerical diagnostic.

### Execution And Verification Plan

Exact prime pairs: sieve plus independent trial division / direct pair enumeration. Evaluate U,V from exact prime endpoints and li differences. Evaluate C independently in two coordinates: nested original hyperbola integration and the product-variable integral

C = integral_(R^2/2)^X log(log(s/R)*log(2s/R)/(log R*log(R/2)))/log s ds.

Derive and document this elementary change of variables; it is a numerical adapter, not a new bound. All comparisons preserve the continuous corner X/R<u<R, whose sharp measure is zero.

Primary sign certificates will use directed decimal intervals, the convergent logarithmic-integral difference series and explicit quadrature error bounds, or exact rational enclosures. A binary64 alternate implementation is an independent diagnostic, not by itself a certificate. Higher precision and finer quadrature will be checked at important extrema. The optional Arb package is unavailable after actual network-denied installation attempts; no Arb execution is claimed.

Check small complete wheels (R=2..16) by exact Fraction arithmetic, separate physical and virtual ledgers then reunite; at larger tested R use the certified compensated floor source, not exponential cube enumeration. Independently check the specific upstream witnesses R=2,3,5,14 and Owner R=10 without repeating unchanged large tables. Preserve historical triangle, finite Euler mass, every other owner and D_R in the full return; reconstruct all six cross terms when squaring a four-part decomposition.

Stop after the registered informative range. If hypotheses fail, preserve minimal certificates and state a corrected structural question. No RH, uniform target bound, independently reviewed paper proof, or Lean certification is claimed in advance.
