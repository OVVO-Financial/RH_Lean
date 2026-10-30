# RH_Lean agent daily report - 2026-10-30 / RH | Finite Wheel & Incidence

**Status:** COMPLETED
**Invocation:** scheduled run begun 2026-10-30 00:09 America/New_York
**Final authority refresh:** 2026-10-30 America/New_York
**Pinned live main:** `d6b59b3fac72e5813145bc1955151e1c8e93e4c6`
**Authority blobs:** `AGENTS.md` `d30a5c4320bec77a510932e72ce7f17d98a68e51`; `CURRENT_PROOF_CONTRACT.md` `7a067ec0423a998e1079e37494061346d8ee02b0`
**Material source blobs:** `research/EULER_FRACTIONAL_COUPLED_20261027.lean` `e6c4b1690e497760d366e36b28a1f7aa60e19f85`; square-clock directive `d275035a5a7de919b31948d58f0341627a877461`; quadratic shift orthogonality `a0c2817d7ae43e4cf67d5d7a3f3bccc9a5f6c285`
**External inbox:** `038018145c0fddb2f6306c0712373adf9cd1ea52`, no handoff newer than 2026-10-18
**New claim:** `20261030-wheel-1`
**Result classes:** `PAPER_PROOF / EXACT ORIGINAL-SOURCE 2-ADIC PACKET IDENTITY`, `PAPER_PROOF / EXACT LOW-HIGH MIXED COVARIANCE`, `PAPER_PROOF / SHARED-2 RESONANT FAMILY`, `FINITE_COMPUTATION`, `NO_FIXED_ETA_GAIN`, `NO_RH`

## A. Main result

### Claim `20261030-wheel-1`: exact prime/even-semiprime conservation packet

Write

```text
X_R = R^2 - 1
f_d(R) = (X_R mod d)/d
m_d = d^(-1) sum_(r mod d) f_d(r)
F_d(R) = f_d(R)-m_d.
```

Group the literal strict source `2*eulerFractionOffQ(R)` by product `d=ab`,
with `alpha_d=sum_(1<=a<b,ab=d) mu(a)mu(b)`. For every odd prime `p` and
root `R>2p`, the complete original packet at `d=p,2p` is

```text
B_p(R) = 2*alpha_p*f_p(R) + 2*alpha_(2p)*f_(2p)(R)
       = -2*f_p(R) + 4*f_(2p)(R).
```

Then, exactly,

```text
B_p(R) is in {0,2};                                          (1)
m_(2p) = 1/4 + m_p/2;                                        (2)
-2*m_p + 4*m_(2p) = 1;                                       (3)
b_p(R) := B_p(R)-1 = -2*F_p(R)+4*F_(2p)(R) is in {-1,1};      (4)
(1/(2p)) sum_(R mod 2p) b_p(R)^2 = 1.                        (5)
```

Thus the negative prime principal debt from `20261029-wheel-1` has an exact
immediate even-semiprime compensator. The pair does not cancel to zero: it
conserves one unit of principal mass and one unit of centered variance.

## B. Cubefree incidence and proof

If `alpha_d` is nonzero, unique factorization forces `d=s^2*t`, with `s,t`
squarefree and coprime. Every prime in `s` occurs in both factors; every prime
in `t` is allocated to exactly one factor. Therefore, for `t>1`,

```text
alpha_d = mu(t)*2^(omega(t)-1),                              (6)
```

while `t=1` gives only the excluded equality `a=b=s`, hence `alpha_d=0`.
In particular `alpha_p=-1` and `alpha_(2p)=+2`.

Put `y=X_R mod p`, `delta=X_R mod 2`, and `x=X_R mod (2p)`. CRT says `x`
is the unique member of `{y,y+p}` having parity `delta`. Thus `x-y` is `0`
or `p`, and

```text
B_p(R) = -2*y/p + 4*x/(2p) = 2*(x-y)/p.
```

This proves (1). As `R` runs modulo `2p`, each residue modulo `p` has one
even and one odd lift. For fixed `y`, the corresponding `2p` remainders are
`y` and `y+p`, with sum `2y+p`. Averaging proves (2), then (3)-(5).

This explains the earlier finite observations at `d=3,6` and `d=5,10`:
the two principal increments sum to exactly one for every odd prime.

## C. Exact low/high mixed-energy ledger

Let `v_p` be the complete-period variance of `F_p`, and put

```text
L_p=-2*F_p,  H_p=4*F_(2p),  b_p=L_p+H_p.
```

For the two parity lifts above each residue modulo `p`, `F_p` is unchanged
and `b_p` changes sign. Hence, for normalized complete-period brackets,

```text
<F_p,b_p>_(2p) = 0,
||L_p||^2_(2p) = 4*v_p,
||H_p||^2_(2p) = 1+4*v_p,
<L_p,H_p>_(2p) = -4*v_p,
||L_p+H_p||^2_(2p) = 1.                                    (7)
```

For a cutoff `Q`, every prime `Q/2<p<=Q` lies below the cut while `2p` lies
in the first high layer `Q<2p<=2Q`. If `2Q<R`, all original occurrences
`(1,p),(1,2p),(2,p)` are admitted. The cut therefore separates the two
halves of (7). A theorem declaring this low/high mixed block zero,
nonnegative, or dispensable is false on the original carrier.

This does not prove that triangle inequality is globally too expensive by a
fixed power. It identifies the exact cancellation that it discards.

## D. Shared-2 resonance and coherent family

Define

```text
S_p = sum_(r mod p) (-1)^((r^2-1) mod p).
```

The binary centered packet satisfies
`b_p(R)=(-1)^(R+((R^2-1) mod p))`. For distinct odd primes `p,q`,
conditioning on the common parity coordinate and applying CRT gives

```text
<b_p,b_q>_(2pq) = S_p*S_q/(p*q).                            (8)
```

If `p=1 mod 4`, then `S_p=1`: the `r=0` term contributes one and the
two-to-one nonzero square residues pair by `z <-> p-z`; since `-1` is a
square and paired representatives have opposite parity, they cancel. Thus,
for `p,q=1 mod 4`,

```text
<b_p,b_q>_(2pq) = 1/(p*q) > 0.                              (9)
```

The high moduli satisfy `gcd(2p,2q)=2`, `lcm(2p,2q)=2pq`, and

```text
<4F_(2p),4F_(2q)>_(2pq)=1/(p*q).                            (10)
```

All other cross terms in the packet expansion have coprime moduli and zero
complete-period covariance. Equations (9)-(10) are therefore a legitimate
positive shared-2 resonance. In a dyadic layer `Q/2<p,q<=Q`, the lcm lies in
`(Q^2/2,2Q^2]`, the long-period scale when `Q^2` exceeds the interval length.
Classical PNT in the progression `1 mod 4` gives about `Q/(4 log Q)` such
primes, but no asymptotic count is needed for the exact identities.

The coherent uncentered packet has mean equal to its number of primes, so its
complete-period energy is at least the square of that number. This refutes an
`O(HQ)`-style uncentered estimate for sufficiently large packets, but not the
sharp-shell target; full-source compensation remains possible.

## E. Test of claim `20261029-analytic-2`

The scheduled Analytic continuation, blob
`2480e5f2b5f0f1bbb5144a79583fd3b89dcf2aa9`, proposes a centered
incomplete-window bound from the product-frequency map

```text
(h,k) -> b*h+a*k mod D,  d=g*a, e=g*b, D=g*a*b.
```

The finite group count is consistent: the map is well-defined and onto, and
its kernel has size `g` because its domain has `de=gD` elements. Today's
packet does not falsify the centered claim. It supplies the requested even
shared-gcd stress test: the `g=2` zero mode is nonzero with weighted value
`1/(pq)`; the within-packet mixed covariance is `-4v_p`; restoring principal
modes changes the packet mean from zero to one.

Thus `20261029-analytic-2` remains `PAPER_PROOF_NEEDS_INDEPENDENT_REVIEW`.
This result neither promotes it to Lean nor refutes its stated scope. It does
refute extensions deleting principal reconstruction, the shared-2 zero mode,
or the low/high mixed term.

## F. Exact finite regression

Exact-rational CPython 3.12.13 assertions checked (1)-(7) for
`p=3,5,7,13,17,29,41,101,149`. Examples:

| p | m_p | m_(2p) | v_p | low energy | high energy | mixed covariance | packet variance |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 5 | 2/5 | 9/20 | 14/125 | 56/125 | 181/125 | -56/125 | 1 |
| 13 | 6/13 | 25/52 | 18/169 | 72/169 | 241/169 | -72/169 | 1 |
| 17 | 8/17 | 33/68 | 32/289 | 128/289 | 417/289 | -128/289 | 1 |

It also checked (9) exactly:

| p | q | lcm(2p,2q) | covariance |
|---:|---:|---:|---:|
| 5 | 13 | 130 | 1/65 |
| 5 | 17 | 170 | 1/85 |
| 13 | 17 | 442 | 1/221 |
| 17 | 29 | 986 | 1/493 |
| 29 | 41 | 2378 | 1/1189 |

Held-out intervals `H=Q^2`, `H<=R<2H`, for `Q=50,100,200,400` retained
packet values in `{0,2,...,2#P}` and displayed the predicted negative mixed
term. These computations are evidence only; Sections B-D are the proof.

Repository search found the cubefree coefficient formula, the prime-only
principal bound, and finite compensation at `d=6,10,12`. It did not find
(1), principal conservation (3), mixed ledger (7), or family (8)-(10).

## G. Continuity, authority, and GitHub state

All named 2026-10-30 reports were absent at intake: `TODAY=PENDING`. The
complete 2026-10-29 set is `YESTERDAY=CARRY_FORWARD`:

- Coordinator mirrors `a6b758112539d0841472082a69da3a4ce49d79cb`, claim `20261029-coordinator-1`;
- Owner `86f69ecbf9a921b9d26424a3e4936c950cabdab5`, claim `20261029-owner-1`;
- Analytic `2480e5f2b5f0f1bbb5144a79583fd3b89dcf2aa9`, claims `20261029-analytic-1..2`;
- Wheel `27b957207d399a1d6c4187b6bfab72433be5a52d`, claim `20261029-wheel-1`;
- Census `00de1c235982179677834940d270357999b75d42`, claim `20261029-census-1`;
- Referee `9c0e84cb7b7303d501c33550697b45c5ded3a46a`, claims `20261029-referee-1..3`;
- Lean `7296e00bf6e606a53af8acc35a11f24a5a99a58f`, claim `20261029-lean-1`.

The external inbox has no claim newer than 2026-10-18; its older PNT, Hecke,
and source no-go handoffs do not state or pay this identity.

At final refresh, main remained `d6b59b3fac72e5813145bc1955151e1c8e93e4c6`;
#1051/#1052/#1053 are merged and there are no open or draft PRs. Compiled
main certifies the named #1051/#1052 declarations, not `20261030-wheel-1`.

No source, proof branch, PR, issue, workflow, schedule, permission, or another
agent's report was modified. The only writes were this authorized report.

## H. Handoff and resume capsule

**Adversarial Referee:** audit (1)-(10), especially `alpha_(2p)=2`, admission
`R>2p`, the parity-lift average, and conditional-parity proof of (8).

**Lean Verification:** after referee acceptance, formalize the Euclidean carry
dichotomy, `m_(2p)=1/4+m_p/2`, and centered mixed identity (7). Do not include
the PNT-in-AP population sentence in the finite theorem.

**Owner/Analytic:** preserve each `p,2p` packet across the cut or retain its
exact mixed term. The next quantitative question is whether larger `s^2t`
ancestry admits analogous prime-adjoining conservation packets that reduce
the complete high principal bill without restating the target.

**Next Wheel run:** classify `d=p,ell*p` for odd primes `ell`; determine
whether `ell=2` is the unique binary law, and seek a disjoint packet cover of
a positive high-layer proportion without double-spending occurrences.

**Independent structural progress:** YES.
**Independent fixed-eta signed progress:** NONE.
**Canonical theorem, complete source payment, strict exponent below 7/8, and RH:** OPEN.

## I. Publication record

Early checkpoint commit `5928e77fe3b0aeabc087a62595d01c6ddb3c099d`,
read back as blob `93d2994086e7571e94c7dba5515f9e584e77529d`.

Completed synthesis commit `6d33881f1cc4c1b918bb7f896af9359869c40cc6`, read back as blob `7c21433b0ec64b709780bba5d54bfa3563b37303` (10,296 characters; `COMPLETED`, claim ID, equation (10), and no non-whitespace control characters verified). This receipt changes no mathematics.


## J. 12:09 America/New_York continuation after live-state change

**Continuation refresh:** 2026-10-30 12:09 America/New_York  
**Updated live main:** `82d00c18f22bbf284fa4c511880f4ebdd9d0f729` (merged #1054)  
**New main source:** `research/EULER_ODD_DOUBLING_PACKET_20261030.lean` blob `053e8f08794c85d127de5c687b03decb0d4807cd`  
**New live drafts inspected:** #1055 head `cb8bdecaf71deba72e2ca88e324aefc2a50b10dc`; stacked #1056 head `3c0b0c4e7fc68b7cd0b5513c45228c4d36d338e0`; stacked #1057 intake head `d00b15b8d6e8b2d708baeb9d8c91f6c636330c3e`; final observed head `2035f1f95b133dd8eb74822a9c1ee28a321aeea7`  
**New claim:** `20261030-wheel-2`  
**Result classes:** `PAPER_PROOF / GENERAL PRIME-ADJOINING COEFFICIENT TRIPLE`, `PAPER_PROOF / COHERENT ODD-PRIME PACKET FAMILY`, `COUNTEREXAMPLE_TO_ODD-PRIME BINARY CONSERVATION`, `FINITE_EXACT_REGRESSION`, `NO_MOMENT_COUNTEREXAMPLE`, `NO_FIXED_ETA_GAIN`, `NO_RH`

The earlier report was complete against its intake state. After it landed, #1054
merged and #1055--#1057 opened. This continuation consumes that changed state
instead of repeating the accepted 2-adic computation. Today's Coordinator,
Owner, and Analytic reports remain `TODAY=PENDING`; today's Census, Referee,
and Lean reports are present at blobs `487d03f121186edf4da60c10d0843347e4c050a0`,
`c76e6a3e1f4c88e5185dac65966e0fe6c8947999`, and
`0c6b9c81fc35529abea32ce8617372ef8b282ade`.

### Claim `20261030-wheel-2`: exact odd-prime adjoining triple

Let
[
  alpha_n=sum_{substack{1le a<b\ab=n}}mu(a)mu(b),
  qquad c=mu*mu.
]
Unique factorization gives the exact identity
[
  c(n)=2alpha_n+
  {f 1}_{n=k^2}mu(k)^2.                                  	ag{11}
]
If (ell) is prime and (ell
mid d), multiplicativity and
(c(ell)=-2, c(ell^2)=1) therefore give
[
egin{aligned}
 alpha_{ell d}
   &=-2alpha_d-{f 1}_{d=k^2}mu(k)^2,\
 alpha_{ell^2d}&=alpha_d.                                	ag{12}
end{aligned}
]
This is the general prime-adjoining version of the uniform 2-adic coefficient
law in draft #1056. For distinct primes (p,ell),
[
 (alpha_p,alpha_{ell p},alpha_{ell^2p})=(-1,2,-1).      	ag{13}
]
Thus the genuine completed occurrence packet is
[
 2alpha_p K_{ell,p}(R),qquad
 K_{ell,p}=f_p-2f_{ell p}+f_{ell^2p}.                    	ag{14}
]

For an arbitrary integer numerator (X=pq+r, 0le r<p), write
(t=qmodell^2) and (u=qmodell). Direct Euclidean division yields
[
 K_{ell,p}(X)
 =rac{(ell-1)^2r}{ell^2p}
   +rac{t-2ell u}{ell^2}.                               	ag{15}
]
Unlike the (ell=2) binary packet formalized by #1054, (15) retains both
the residual coordinate and an (ell^2)-quotient coordinate. In particular
there is no odd-prime analogue of a pointwise two-value packet with constant
centered square.

### Coherent genuine square-clock family

Fix an odd prime (ell) and choose distinct primes
(p_1,ldots,p_Nequiv1pmod{ell^2}), all greater than (ell^2), with
(Nge2). Put (P=prod_i p_i) and take the genuine root
[
 R=P+1,qquad X_R=R^2-1=P(P+2).
]
Every product (ell^2p_i<R), so all three original columns in (13) are
fully admitted. Moreover
[
 rac{X_R}{p_i}=(P/p_i)(P+2)equiv3pmod{ell^2}.
]
Consequently all (N) distinct prime-adjoining packets have exactly the same
value:
[
 K_{ell,p_i}(R)=
 egin{cases}
  1/3,&ell=3,\
  -3(2ell-1)/ell^2,&ellge5.
 end{cases}                                                	ag{16}
]
Their contributions to the literal twice-off-diagonal source are respectively
(-2/3) or (6(2ell-1)/ell^2) per prime. Dirichlet's theorem supplies
arbitrarily large finite choices of the (p_i), so (16) is a coherent family,
not an isolated residue accident.

This refutes any proposed odd-prime packet argument that asserts pointwise
sign balance, packet independence, or a uniform constant-energy conservation
law analogous to #1054. It does **not** refute #1056's paper-level interval
moment: the construction is one sparse root, and the claimed bound explicitly
allows incomplete-period mass. It is a mandatory stress family for any
attempt to improve the (Q^3) completion term or to sum prime-adjoining
packets before restoring the remaining source.

### Independent audit of draft #1056

I checked the paper steps behind
[
 sum_{Rin I}|Z_Q(R)|^2
 ll_arepsilon H Q^{1+arepsilon}+Q^{3+arepsilon}.
]
The even-modulus Gauss estimate follows exactly by differencing (x=y+t);
the inner sum survives for precisely (gcd(2k,m)) values of (t). The
product-frequency fibre has size (4gcd(d,e)), and
(4gcd(d,e)operatorname{lcm}(4d,4e)=16de), giving the stated incomplete
term. Finally
[
 sum_{d,ele Q}rac{gcd(d,e)}{sqrt{de}}ll Qlog Q
]
by (d=ga,e=gb), while the one-variable incomplete mass is
(O_arepsilon(Q^{3/2+arepsilon})).

No contradiction was found. The result remains exactly
`PAPER_PROOF_NEEDS_INDEPENDENT_REVIEW`, because the all-frequency Fourier
assembly and epsilon-uniform divisor estimates are not named Lean theorems.
Draft #1057 is a distinct exact divisor-synthesis lane and does not pay the
primitive (h=1) source.

### Exact regression and handoff

Exact rational checks used:
- (ell=3), (p=(19,37,73)), (R=51320):
  each (K=1/3), total twice-source contribution (-2);
- (ell=5), (p=(101,151,251)), (R=3828002):
  each (K=-27/25), total twice-source contribution (162/25).

The local reproducer SHA-256 was
`770c987a06a154242cbe92c497f936d8cac545e49924cf4509df85c47e4b2fe2`.
It is finite evidence; equations (11)--(16) are the proof.

**Analytic/Referee handoff:** include (16) as the odd-prime coherent-mode
falsifier for any proposed (Q^3) improvement. A successful estimate must
average this progression through complete/incomplete windows rather than
assert cross-packet cancellation.

**Lean handoff:** after review and after the stacked coefficient definitions
reach main, (11)--(12) are the smallest nonduplicate formal target. Do not
formalize the Dirichlet population statement as part of the finite coefficient
lemma.

**Independent structural progress:** YES.  
**Independent fixed-(eta) signed progress:** NONE.  
**Canonical theorem, complete source payment, strict exponent below (7/8),
and RH:** OPEN.


## K. 18:08 America/New_York continuation after merged #1059

**Status:** COMPLETED continuation  
**New claim:** `20261030-wheel-3`  
**Result classes:** `PAPER_PROOF_NEEDS_INDEPENDENT_REVIEW / EXACT COMPLETE OWNER-FIBRE FAMILY`, `INFINITE COHERENT SIGNED-RETURN OBSTRUCTION`, `NO_NEW_FIXED_ETA_BOUND`, `NO_RH`

Live `main` is `6b2a869750b92fcdbebff78a591e7722b4f2c747`, the merge of #1059. There are no open or draft PRs. Authority blobs are `AGENTS.md` `d30a5c4320bec77a510932e72ce7f17d98a68e51` and `CURRENT_PROOF_CONTRACT.md` `7a067ec0423a998e1079e37494061346d8ee02b0`. The source declarations used below are:

- `research/COVARIANCE_REMAINDER_OWNER_FUBINI.lean` `a1292825681d028ec511059920274e62e1168638`;
- `research/COVARIANCE_RECIPROCAL_OWNER_CONGESTION.lean` `d58e9f9b13c251a73b861af52b0d9288251e442f`;
- `RHLean/Analysis/PrimeWheelRunOthelloBoundary.lean` `26ffb242dc294fe8f57c1d6b8985c5f70f4e3d43`;
- `research/OWNER_RECIPROCAL_EXPONENT_SLACK_20261030.lean` `8386033011145cae64961482e273598d5a6a3263`;
- `research/OWNER_COMPLETE_SIGNED_RETURN_20261030.lean` `3a35c851336ea6c357c65217a0d1dc521557c3bc`;
- `research/OWNER_SIGNED_RETURN_ATTACK_20261030.md` `56d22ec7b4cc9266bcf2f3c81cef52c4d42c8624`.

Today's Coordinator and Owner files are absent at final intake and remain `TODAY=PENDING`. Today's Analytic, Census, Referee and Lean reports were consumed at blobs `bae5e244f4bafdb42071263e72d502d50f3ce31e`, `21449e1bef548daccfc88b0ceb9bd26ded392971`, `482e44efaaca567878129d539251a427580824be`, and `0c6b9c81fc35529abea32ce8617372ef8b282ade`. Yesterday's Coordinator and Owner reports were consumed as `YESTERDAY=CARRY_FORWARD` at `a6b758112539d0841472082a69da3a4ce49d79cb` and `86f69ecbf9a921b9d26424a3e4936c950cabdab5`. External inbox blob `038018145c0fddb2f6306c0712373adf9cd1ea52` has no claim newer than 2026-10-18.

### Claim `20261030-wheel-3`: the complete prime parent fibres have unbounded coherent return

Let `q` be prime and let `W >= q^2`. For the genuine original parent `u=(1,q)), the complete recursive child fibre is exactly

[
  mathcal F_W(1,q)
  =
  {(1,pq),(p,q): p<q, p {m prime}}.
]

Equivalently, for every natural `p`,

[
 k_W((1,q),p)=
 egin{cases}
 2,&p {m prime}, p<q,\
 0,&	ext{otherwise}.
 end{cases}
]

This is an equality of original occurrence identifiers, not merely a count. Consequently

[
 operatorname{ownerReturnHarmonicMultiplicity}(W,(1,q))
   =2sum_{p<q, p {m prime}}rac1p,
]
and, since the parent reciprocal amplitude is (-1/q),

[
 sum_{vinmathcal F_W(1,q)} a(v)
   =rac2qsum_{p<q}rac1p,
 qquad
 rac{left|sum_{vinmathcal F_W(1,q)}a(v)ight|}
      {|a(1,q)|}
   =2sum_{p<q}rac1p.
]

Euler divergence of the prime harmonic series therefore gives the quantified no-go

[
 orall C>0 exists q {m prime} exists Wge q^2:
 left|sum_{vinmathcal F_W(1,q)}a(v)ight|>C|a(1,q)|.
]

Thus the #1059 `(1,7)` witness is not an isolated small obstruction. No uniform per-parent signed-return contraction, no bounded Schur row sum, and no transfer from the reciprocal-square congestion to the coherent signed square can hold on all genuine fibres. This does not refute cancellation between distinct parents or cancellation with the retained terminal population.

### Proof and source-admission audit

For each prime `p<q`, both displayed children are squarefree and have nonzero Möbius weight. Their differing-prime set is exactly `{p,q}`, so the least separating prime is `p`. Removing `p` gives the ordered parent `(1,q)` in both cases. The pairs are coprime: `gcd(1,pq)=1` and `gcd(p,q)=1`; hence neither is removed by the common post-root-prime carrier. The endpoint inequalities are `1<pq<q^2<=W` and `p<q<=W`.

Conversely, the compiled two-candidate theorem says a fixed-owner child can only be `(1,pq)` or `(p,q)`. Owner chronology in a child of parent `(1,q)` forces `p<q`; nonzero squarefree ownership forces `p` prime. This proves coverage, disjointness and absence of extra children. The two children for different primes are distinct, so no occurrence is spent twice.

Both children have Möbius product (+1), whereas the parent has product (-1). Therefore all children in the complete fibre have the same sign. The exact reciprocal-square diagonal factor remains

[
  2sum_{p<q}p^{-2}le79/81
]

by the on-main congestion theorem, while the coherent amplitude factor (2sum_{p<q}p^{-1}) is unbounded. This is an arbitrarily large separation between the certified diagonal contraction and the complete signed return.

### Exact regression and falsification

Exact rational checks reproduce #1059 at `q=7` and extend it:

| `q` | number of owners | coherent factor (2sum_{p<q}1/p) | coherent square ratio | diagonal factor (2sum_{p<q}1/p^2) |
|---:|---:|---:|---:|---:|
| 7 | 3 | `31/15` | `961/225` | 0.802222... |
| 11 | 4 | `247/105` | 5.533696... | 0.843038... |
| 101 | 25 | 3.605634... | 13.000599... | 0.900857... |
| 1009 | 168 | 4.396160... | 19.326224... | 0.904240... |
| 10007 | 1229 | 4.966119... | 24.662346... | 0.904475... |

The computation is only a regression; the all-scale conclusion uses the exact fibre proof and the classical divergence theorem. Boundary cases were checked: `p=q` fails strict chronology and `p>q` has owner `q), not `p`; `W< p q` may clip a child, which is why the theorem assumes `W>=q^2`; composite `p` is not an owner; repeated-prime candidates are nonsquarefree.

Repository code search found only the concrete `q=7,W=35` complete-fibre theorem and no equivalent all-prime fibre formula or unbounded harmonic-return theorem. The result is therefore new relative to current `main`, subject to independent review.

### Proof impact and next lemma

This closes a structural question negatively: local owner incidence cannot by itself turn the positive reciprocal exponent slack into a complete signed-return gain. Any successful `T+A` estimate must use cross-parent cancellation, the terminal population, or an additional global arithmetic restriction. Packetwise diagonal contraction and per-parent Schur contraction are now both invalid globalization mechanisms.

Smallest formalization target: for prime `q`, prime `p<q`, and `W>=q^2`, prove

[
 operatorname{postRootCovarianceFixedOwnerChildFiber}(W,(1,q),p)
 ={(1,pq),(p,q)}.
]

Then prove the zero case for nonprime or `q<=p`, the exact finite harmonic-multiplicity identity, and only afterward import the already-standard divergence of `sum_{p<q}1/p` if the library theorem is available. Keep the global no-go paper-level until that last step is independently reviewed.

**NO_NEW_INDEPENDENT_INEQUALITY** toward the sharp-shell fixed-`eta` upper bound.  
**Canonical theorem, strict exponent below 7/8, complete source payment, and RH:** OPEN.
