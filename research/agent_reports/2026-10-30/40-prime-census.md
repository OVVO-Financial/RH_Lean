# RH_Lean agent daily report - 2026-10-30 / RH | Prime Census Laboratory

**Status:** COMPLETED  
**Invocation:** scheduled run begun 2026-10-30 01:51 America/New_York  
**Final authority refresh:** 2026-10-30 01:58 America/New_York  
**Pinned live main:** `d6b59b3fac72e5813145bc1955151e1c8e93e4c6`  
**Authority blobs:** `AGENTS.md` `d30a5c4320bec77a510932e72ce7f17d98a68e51`; `CURRENT_PROOF_CONTRACT.md` `7a067ec0423a998e1079e37494061346d8ee02b0`; square-clock directive `d275035a5a7de919b31948d58f0341627a877461`  
**Material source blobs:** `research/EULER_FRACTIONAL_COUPLED_20261027.lean` `e6c4b1690e497760d366e36b28a1f7aa60e19f85`; sharp localization `1f5b2e57f24e44e5b7b5cea80d437ac8350365b0`  
**External inbox:** `038018145c0fddb2f6306c0712373adf9cd1ea52`, no handoff newer than 2026-10-18  
**New claim:** `20261030-census-1`  
**Evidence classes:** `PAPER_PROOF / EXACT ORIGINAL-SOURCE ODD-DOUBLING PACKET`, `FINITE_COMPUTATION`, `REFUTED_STRENGTHENING`, `NO_FIXED_ETA_GAIN`, `NO_RH`.

## A. Main result

### Claim `20261030-census-1`: the Wheel prime/even-semiprime packet extends to every odd admitted product modulus

Let

```text
X_R = R^2-1,
f_d(R) = (X_R mod d)/d,
m_d = d^(-1) sum_(r mod d) f_d(r),
F_d = f_d-m_d,
alpha_d = sum_(1<=a<b, ab=d) mu(a)mu(b).
```

For every odd `d` with `alpha_d != 0`, the literal grouped terms of
`2*eulerFractionOffQ` at `d` and `2d` satisfy

```text
alpha_(2d) = -2*alpha_d.                                      (1)
```

If both product moduli are admitted by the physical cutoff, define

```text
C_d(R) = 2*alpha_d*f_d(R) + 2*alpha_(2d)*f_(2d)(R).
```

Then, exactly,

```text
C_d(R) is in {0,-2*alpha_d},                                  (2)
m_(2d) = 1/4 + m_d/2,                                         (3)
mean_(R mod 2d) C_d(R) = -alpha_d,                             (4)
C_d(R)+alpha_d is in {-|alpha_d|,+|alpha_d|},                  (5)
mean_(R mod 2d) (C_d(R)+alpha_d)^2 = alpha_d^2.                (6)
```

Writing `L_d=2*alpha_d*F_d`, `H_d=2*alpha_(2d)*F_(2d)` and
`v_d=mean F_d^2`, the exact complete-period low/high ledger is

```text
<L_d,H_d>_(2d) = -4*alpha_d^2*v_d,
||L_d||^2_(2d) = 4*alpha_d^2*v_d,
||H_d||^2_(2d) = alpha_d^2 + 4*alpha_d^2*v_d,
||L_d+H_d||^2_(2d) = alpha_d^2.                               (7)
```

Thus `20261030-wheel-1` is the special case `d=p`, `alpha_p=-1`.
The conservation law is not prime-specific: it covers every odd cubefree
product ancestry with nonzero original coefficient. Composite packets such
as `(15,30)`, `(21,42)`, `(33,66)`, `(35,70)`, and `(39,78)` are often among
the largest physical low/high interactions.

## B. Proof

The unique nonzero factorization is `d=s^2*t`, with `s,t` squarefree,
coprime and `t>1`, and

```text
alpha_d = mu(t)*2^(omega(t)-1).
```

Because `d` is odd, multiplying by 2 adjoins a new prime to `t`; it flips
`mu(t)` and doubles the unordered complementary-factor multiplicity. This
proves (1).

Put `y=X_R mod d` and `x=X_R mod 2d`. CRT gives `x-y` in `{0,d}`. Hence

```text
C_d(R) = 2*alpha_d*y/d - 4*alpha_d*x/(2d)
       = -2*alpha_d*(x-y)/d,
```

which proves (2). The two lifts of each root residue modulo odd `d` have
opposite parity, so their `2d` remainders are `y` and `y+d`. Averaging gives
(3)-(6). Moreover `F_d` is fixed on the two lifts while the centered packet
changes sign, so `<F_d,L_d+H_d>_(2d)=0`. Expanding this identity and (6)
gives (7).

No prime distribution theorem, randomness, Mertens bound, OAI exponent, or
asymptotic approximation enters this proof.

## C. Preregistered experiment

**Mystery.** The Coordinator localized the first unpaid bill to the
high-product range above `Q=floor(sqrt H)`, while today's Wheel report found
an exact split `p,2p` cancellation across that cut. Does that prime packet
explain the first high layer, or is the observed mixed term mainly generic
shared-frequency resonance?

**Competing hypotheses.** `H1`: prime/even-prime packets dominate the
negative centered low/high interaction. `H2`: generic shared-factor and
adjacent-modulus resonances remain comparable, so the prime identity is only
a small special case. A third outcome was that a broader exact ancestry
packet, not prime status, controls a large fraction.

**Carrier.** For each root interval `H<=R<2H`, put
`Q=floor(sqrt H)`. The low layer uses every nonzero original grouped modulus
`2<=d<=Q`; the first high layer uses `Q<d<=2Q`. Since `2Q<R` in every tested
case, all factor pairs are physically admitted and the grouped coefficient
is exactly the original unordered-pair sum. No moving occurrence is inferred
from divisibility alone.

The exact uncentered low/high inner product was decomposed into

```text
H*P_low*P_high
+ P_low*sum H_centered + P_high*sum L_centered
+ <L_centered,H_centered>.
```

The centered term was then decomposed by every modulus pair, with the exact
odd-doubling packets separated. Within each layer, diagonal and off-diagonal
energies were also reconstructed, and recombination was checked exactly.

## D. Exact computation and cross-checks

Implementation A reconstructs `alpha_d` from `d=s^2*t`. Implementation B
independently enumerates all unordered physical factor pairs `a<b`, `ab=d`,
using a Möbius sieve. The coefficient arrays agreed at every tested modulus.
All means, columns, products and energies use Python `Fraction`; no floating
point is used for any assertion.

The identity regression independently checked (1)-(7) for all 463 odd
nonzero moduli `d<=999`, every residue `R mod 2d`, using the pair-enumerated
coefficients. The layer census checked exact reconstruction at

```text
H = 64,127,256,317,512,900,1027,1600,2048.
```

Reference environment: CPython 3.12.14. Script SHA-256
`31c4cd7a27df21eef9713704942548e4ef19ef0120cf6fbf733d04233e0c0e40`.
Canonical exact result checksum:
`478d584e2b28b9c65a962e2c63d7e2786332ded147aa6b149552bbe9a20841b4`.

## E. Results

The table displays decimal renderings of exact rational sums. `packet` is
the sum of matched odd `(d,2d)` centered cross terms only.

| H | Q | centered low/high | odd-doubling packet | packet share | full uncentered cross |
|---:|---:|---:|---:|---:|---:|
| 64 | 8 | -91.512 | -49.572 | 0.542 | -217.095 |
| 127 | 11 | -211.700 | -84.999 | 0.402 | -187.907 |
| 317 | 17 | -1089.590 | -752.558 | 0.691 | -1099.331 |
| 900 | 30 | -4631.456 | -2742.081 | 0.592 | -17269.730 |
| 1027 | 32 | -5935.337 | -3452.231 | 0.582 | -27195.045 |
| 2048 | 45 | -24831.333 | -13667.355 | 0.550 | -57138.845 |

Across all nine fixed cases, the odd-doubling packets account for 40.2% to
69.5% of the centered low/high interaction. This is substantial but not a
complete explanation.

At `H=317`, exact recombination gives low uncentered energy `1332.156293...`,
high energy `4650.610260...`, cross `-1099.330745...`, and combined energy
`3784.105062...`. At `H=1027` the corresponding values are
`21403.423617...`, `65207.636356...`, `-27195.044679...`, and
`32220.970615...`. Treating the layers by separate norms loses a large
original signed interaction.

Shared ancestry, not adjacency, produces the extremes. At `H=1027`, the
largest shared-factor terms include `(14,42)=-1767.451...`,
`(30,60)=-1715.612...`, and the odd-doubling packet
`(21,42)=-1636.412...`. The strongest adjacent pair is only
`(30,33)=+85.060...`; the strongest coprime pair is
`(30,53)=+124.916...`. At the primorial-aligned cut `H=900,Q=30`, the
same shared-factor hierarchy persists.

## F. Falsification and scope

**Refuted interpretation:** the Wheel conservation is a prime-only effect.
The proof shows it for every odd nonzero product ancestry, and the physical
census places composite packets among the largest terms.

**Refuted interpretation:** odd-doubling packets exhaust the mixed bill.
The nonpacket remainder is 30.5% to 59.8% of the centered cross term in the
tested cases. Large pairs such as `(14,42)` and `(30,60)` require additional
prime-adjoining/shared-square analysis.

**Refuted strengthening:** `<L_d,H_d>` is nonpositive on every incomplete
window. Already for `d=3`, `alpha_3=-1`, the one-point window beginning at
`R=2` has mixed product `20/81>0`. Equation (7) is a complete-period theorem;
the observed negative dyadic packet sums are `FINITE_COMPUTATION`, not an
all-window sign law.

The fixed cases support no asymptotic percentage, universal sign, or
fixed-eta shell estimate. No threshold was fitted after observing the data.

## G. Proof impact

Claim `20261030-census-1` supplies a new exact, source-faithful conservation
law for a positive structured portion of every first high layer. It explains
why the low/high triangle split is physically lossy and identifies the
relevant hidden variable: adjoining the parity prime to an **odd product
ancestry**, rather than prime status.

It does not bound the nonpacket shared-factor remainder, the rest of
`U_R^(>Q)`, moving layers `d>=H`, the fractional diagonal, reciprocal square,
or sharp-shell boundary transfer. It therefore proves no
`H^(5/2-eta+epsilon)` estimate, no exponent below `7/8`, no canonical VF
bound, and no RH.

The next smallest theorem is a general prime-adjoining packet formula for
`d` and `ell*d`, classified by whether `ell` is absent from `t`, present in
`t`, or present in the shared square part `s^2`. The decisive quantitative
question is whether disjoint exact packets cover enough of the first high
layer to leave a remainder with energy below the absolute `H^(5/2)` scale.
The present data warn that shared-factor families must be retained rather
than paid separately.

## H. Continuity and repository state

Today's Finite Wheel report blob
`e0d0291183edf029c636589d828dcaa368189a1c`, claim
`20261030-wheel-1`, was consumed. Today's Coordinator, Owner, Analytic,
prior Census, Referee, and Lean reports were absent at final intake:
`TODAY=PENDING`.

The complete relevant 2026-10-29 set was consumed as
`YESTERDAY=CARRY_FORWARD`:

- Coordinator mirrors `a6b758112539d0841472082a69da3a4ce49d79cb`, claim `20261029-coordinator-1`;
- Owner `86f69ecbf9a921b9d26424a3e4936c950cabdab5`, claim `20261029-owner-1`;
- Analytic `2480e5f2b5f0f1bbb5144a79583fd3b89dcf2aa9`, claims `20261029-analytic-1..2`;
- Wheel `27b957207d399a1d6c4187b6bfab72433be5a52d`, claim `20261029-wheel-1`;
- Census `00de1c235982179677834940d270357999b75d42`, claim `20261029-census-1`;
- Referee `9c0e84cb7b7303d501c33550697b45c5ded3a46a`, claims `20261029-referee-1..3`;
- Lean `7296e00bf6e606a53af8acc35a11f24a5a99a58f`, claim `20261029-lean-1`.

Final live main remains `d6b59b3fac72e5813145bc1955151e1c8e93e4c6`.
There are no open or draft PRs. Merged main certifies the named #1051/#1052
declarations, not `20261030-census-1`, which is a paper proof plus exact
finite regression.

No main source, proof branch, PR, issue, workflow, schedule, permission, or
another agent's report was modified. The only authorized repository write is
this report.

## I. Continuation checkpoint

Do not repeat the nine layer cases or the `d<=999` identity regression.
Resume by deriving the three-case coefficient and CRT law for `(d,ell*d)`
with odd prime `ell`, then search for the smallest legal packet family whose
complete-period covariance has no fixed sign or whose occurrences overlap.
Stop at the first discrepancy between direct unordered-pair reconstruction
and the proposed packet formula. Preserve exact moving admission before
extending beyond `2Q<H`.

**Independent structural progress:** YES.  
**Independent fixed-eta signed progress:** NONE.  
**Canonical theorem, complete source payment, strict exponent below 7/8, and RH:** OPEN.

## J. Publication record

The completed report was created by commit
`6e3553725835bf72574c63390051a9ceeddc6418` and read back as blob
`0633ede5c89255e119bda27f41201eee57502502` (11,571 characters; the
`COMPLETED` marker and claim `20261030-census-1` were verified). This receipt
update changes no mathematics.
