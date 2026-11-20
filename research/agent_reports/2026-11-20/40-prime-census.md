# Prime Census Laboratory | November 20, 2026

## 03:11 EST | Registered experiment

`20261120-census-0311-EST/LEDGER-OPEN` | Scheduled November 20, 2026, 03:11:02 EST (08:11:02Z), America/New_York; RUN_ID_UNAVAILABLE. EXECUTION=IN_PROGRESS. No numerical result at registration.

Coordinator PORT H.4: fix B=1009,1531,2053, b the first squarefree integer >=B, and both inclusive endpoints X=ceil(5b^2/3), floor(7b^2/4). Before inspecting results, partition the signed smooth unique-split mass by largest prime into (b/2,b), (b/3,b/2], (b/4,b/3], (b/5,b/4], and <=b/5. Contrast compensation inside this last band with compensation elsewhere in the original prefix. Report both S/L_b and S_low/L_b+F_5(X/b^2), L_b=b^2/log^2 b; neither six successes nor six misses determines an asymptotic. Split the remaining collar by squarefreeness, roughness and split multiplicity, reinstate the prior history and both ordered tail factors. A single integer mismatch between literal multiplication and an independent divisor sieve stops interpretation. As a structural discriminator, record multi-split excess, not just its site count, before interpreting a signed cancellation. No first-bad premise.

Main `6338941bb9d10387e9361ca3ca55468d4c710e4c`; AGENTS `500b6daed5e867d19d97c30e43a7a1e7d2055a51`; contract `95566e37c8eaeb99ee680660df4f9d2e06ea5038`; Newton source `131e9af86207a42d4bf6488e3f64c9ce4f97e5df`. Reports intake `7471a211745ecb39bccdcfdf28be12f6b72a010c`, November 20 tree `c392141a0b45c9593001f168feb5b19d5e43c091`: this role's canonical path absent. November 20 SLICE, SQUARE, WINDOW received; Coordinator PORT, own CLOCK, Referee ESCAPEMENT and Lean PLATEAU/TWO-WITNESS carried from November 19. No open/draft PR. The latest merged #1152 concerns finite Nyman witnesses, not the MU-LIFT bound. RH remains open.

half_bootstrap_ack=BOOTSTRAP_TO_HALF_V1; cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1; continuity_ack=LAST_ACTUAL_REPORT_CONTINUITY_V1; publish_ack=REPORT_PUBLISH_RECOVERY_V1. Direct Git tunnel HTTP 403; authorized API, own report only. Final findings and the continuation checkpoint will be appended under a distinct marker.

## 03:35 EST | The sign depends on which factors can coexist

`20261120-census-0311-EST/LEDGER-FINAL` | EXECUTION=COMPLETE. LEDGER1,3,4 are finite computations; LEDGER2 is a paper derivation for independent review. No new Lean theorem, exponent, strict-prefix law or RH proof.

**A. Discovery.** The small-prime band returned negative mass at all six registered endpoints, but never canceled the positive mass of the other bands. There is a reason to separate two effects: the small-prime sum counted *per factorization* has a negative leading term, whereas suppressing the sum counted *per integer* requires a positive contribution of a specified size from integers with multiple factorizations. Dropping coprimality reverses the leading sign at both endpoints. That is a restriction on which factors can coexist, not an assumption of independent signs.

**B. Authority and scope.** Main and source pins are in the registration above; no open/draft PR at closing source check. `VFCanonicalSquareVonKochStatement` (blob `79030d70e8d3e0d08eef9bac53fef95c36eca2fb`) asks for one C>=0 such that all integers R>=2 satisfy `|pi(R^2)-vfMidFinishedMass(R)-sqrt(2)| <= C R log R`; its RH consumer retains `ClassicalVonKochRHCriterion`. The present MU-LIFT test concerns the original Mobius source, not the physical VF source. In fixed-family #1119, `native_mertens_near_uniform_window_error_closed` gives every positive loss above `b*=7/8-7/(64 Npack)`, not zero loss at b*. The common slot widths give Npack<=Nstar (6 ell vs 3 ell). We use only the permitted fixed beta=7/8, after restoring LOW, signed HIGH, principal and errors to the native source. #949 identifies the genuine zero boundary; no donor estimate is transferred. Newton and signed-lift blobs: `131e9af86207a42d4bf6488e3f64c9ce4f97e5df`, `af69b4811cf9f523eb7c96fb0ca836b2cdbd1180`.

**C-D. Competing hypotheses and carrier.** Either small primes compensate the other bands already on the unique-split sites, or payment must involve multiple splits or other populations. A changing residual sign was a discriminator; an integer mismatch stopped the test. With `a=mu*1_{n<B}` (pointwise truncation), the original Dirichlet convolutions are `H0=2a-a*a*ones`, `T=(mu-a)*(mu-a)*ones`, `H0+T=mu`. Let D(n) be the number of unordered splits `ij=n`, `b<=i<=j`, with both factors squarefree. Below `2b^2` only the cofactor one is possible. For squarefree n, `T(n)=2D(n)mu(n)`; on squares the ordered diagonal occurs once, and on other squareful sites H0 and T can both be nonzero. S sums mu once over squarefree `P+(n)<b, D(n)=1`; S5 further requires `5P+(n)<=b`. All ranges below have inclusive integer endpoints. Registered b=B in each case.

**E. LEDGER1 | FINITE_COMPUTATION.** Columns 2,3,4,5 below are the first four largest-prime bands in the registration, in descending order. In the last two columns the integer p certifies the value lies in `[p,p+1]*10^-6`; `c=X/b^2`, `L_b=b^2/log^2 b`, and F5 is PORT's leading term for the first four bands.

| B | X | band 2 | band 3 | band 4 | band 5 | S5 | S | S/L_b | S5/L_b+F5 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
|1009|1696802|1879|527|-4|-102|-789|1511|71003|80805|
|1009|1781641|2383|661|-18|-123|-934|1969|92525|102656|
|1531|3906602|3949|1204|-63|-330|-1568|3192|73241|81903|
|1531|4101931|5036|1439|-94|-392|-1915|4074|93479|102606|
|2053|7024682|6384|1715|-206|-655|-3059|4179|57677|75662|
|2053|7375915|8207|2125|-306|-733|-3786|5507|76006|94293|

The next ledger gives signed site sums for smooth D=0, smooth D>=2 (once), rough D=0, rough D=1, and then the signed T on squareful sites. Add the four site columns, S above, and history `M(b^2-1)` to obtain M(X). Independently `H+T=M(X)` where H and T are whole-prefix sums. Rough D>=2 is empty: a factor carrying a prime >=b must equal that prime since each factor is <2b. Two distinct such primes, if present, determine the same split.

| B, end | sm0 | sm2+ | rough0 | rough1 | squareful T | history | H | T | M(X) |
|:--|---:|---:|---:|---:|---:|---:|---:|---:|---:|
|1009 L|-3335|45|3323|-1488|70|135|-161|352|191|
|1009 R|-3698|1|3860|-1832|-19|135|60|375|435|
|1531 L|-7104|83|7197|-3257|42|80|-127|318|191|
|1531 R|-7888|36|7984|-4240|-13|80|119|-73|46|
|2053 L|-10636|313|10406|-4817|-239|244|48|-359|-311|
|2053 R|-11871|331|11358|-6245|-264|244|-268|-408|-676|

On all six, `H^2+2HT+T^2=M(X)^2` exactly; `2HT` switches from -34464 to +218688 across the last two endpoints. This is the ordinary square of this original prefix, not an NNS covariance. The untouched smooth unique sites are not the whole off-mask sum. The genuine EX1 paired counts on the full collar domain are 3837,7603,12492 (by b); clipped net fluxes are -311,-349,-569,-640,-864,-885. EX3 is empty here: its r-window is shorter than its block widths 64,82,98. The complete off-mask signed sums in the six prefixes of the collar are 367,649,680,606,309,-35. Omitting the off-mask remainder changes the answer.

**F. Exceptional cases.** At the last endpoint the low unique sum by number of distinct primes 4,5,6,7 is `4687,-12235,3831,-69`. Removing the five-prime sites reverses the low sign in every registered row. The first negative low multiple-split site at B=1009 is `1144330=2*5*11*101*103=1010*1133=1030*1111`: incidence -2, site -1, `(H0,T,mu)=(3,-4,-1)`. At B=549, b=551, X=506002, the *aggregate* low multiple-split incidence is -5, so finite positivity for all B is false; this is not a first-bad example or a smallest-B claim. At B=1024 and 1025, b=1027 gives the identical low ledger (-778,180) for (S5,V5), but `M(B^2-1)` is respectively 257 and 288. A common post-square ledger does not determine the strict history.

**G-H. LEDGER2 | PAPER_PROOF, self-audited; Referee pending.** Fix any integer X in the registered proportional window, now with B tending to infinity. Put `V5=sum_{squarefree,5P+<=b,D>=2} D mu` on the collar and `W5=S5+V5`. This is incidence, not a once-count or a pair of splits. Let `K(f,g)=sum_{i,j>=b,ij<=X,gcd(i,j)=1} f(i)g(j)` (ordered), `m=mu`, `r(i)=mu(i)1_{5P+(i)>b}`. Each factor is below 2b. Exactly `2W5=K(m-r,m-r)` and `Q5=K(r,r)/2` is a signed prime comparison, not an original extra payment.

For fixed i, the coprime Mobius sum to t is `sum_a M(floor(t/a))`, over a<=t supported on primes of i, including 1 (invert the Euler factors at primes dividing i). Its absolute value is at most `C t^beta E_i`, `E_i=prod_{p|i}(1-p^-beta)^-1`. Expanding the product over squarefree divisors gives `sum_{i<=2b} E_i <= 2b prod_p(1+1/[p(p^beta-1)]) = O_beta(b)`. Sum the inner interval bound with the other factor fixed: for any one-variable |g|<=1, `K(m,g)=O(b^(1+beta))`. Symmetry and expansion give `W5=Q5+O(b^(15/8))`, uniformly in X. This power error is relative to the exact Q5, NOT to its continuous area.

For b>100, each nonzero rough-to-b/5 factor has a unique form kp, where p>b/5 is prime and `k in {1,2,3,5,6,7}`: k<35/4 and squareful k have zero weight. The pair condition is exactly `(k,l)=1, p!=q`; p,q cannot divide the small cofactors. Count these prime pairs with their sign `mu(k)mu(l)`, lower limits `kp,lq>=b` and cutoff `kp*lq<=X`; remove p=q before summing. It costs O(b) in the area limit. Write `h(c,z)=c log(c/z)-c+z` for c>z and 0 otherwise. The fixed-factor PNT gives normalized area `h(c,max(1,k/5)max(1,l/5))/(kl)` per ordered cell: integrate in `u=kp/b,v=lq/b`. Rectangle approximation and monotonicity give uniformity on compact c for each cell before signs are combined. Summing the finitely many coefficients yields, uniformly,

```text
W5/L_b = G5(c)+o(1)
G5(c) = -h(c,1)/5 + 2h(c,6/5)/15 + h(c,7/5)/210 - h(c,42/25)/42.
```

In particular `G5 <= -13h(c,1)/210 < 0`. At c=5/3,7/4 its two micro-enclosures start at -26050,-31005. Without the small-cofactor coprimality condition the respective lower integers are +3,+106: this surrogate even gets the sign wrong. Its coefficients at z=1,6/5,7/5,36/25,42/25,49/25 are `1/1800,-1/180,1/210,1/72,-1/42,1/98`. Only the coprime version represents the squarefree source. PNT reference: Johnston and Yang, arXiv:2204.01980; no short-interval PNT or power rate for this area is assumed.

**I-J. The missing inequality.** PORT1-4's paper formula gives `(S-S5)/L_b=F5(c)+o(1)` uniformly. Combined with LEDGER2, this gives `S/L_b=F5+G5-V5/L_b+o(1)`. Thus uniform `S=o(L_b)` on this mask is equivalent to `V5/L_b=F5+G5+o(1)` uniformly. PORT's lower bound and `G5>=-(1/5+1/42)h(c,1)` give `F5+G5 >= 1/60+(29/105)h(c,1)>0`. At the exact two proportional endpoints the required leading values are in `[91832,91833]` and `[115541,115542]` times 10^-6. This is a necessary positive payment for suppression of this *auxiliary* population, not necessary for RH. The inference using PORT shares its independent-review status.

| B, end | low multi once | V5 (weighted) | Q5 | W5-Q5 | V5/L_b (micro floor) |
|:--|---:|---:|---:|---:|---:|
|1009 L|79|185|-639|35|8693|
|1009 R|86|226|-727|19|10620|
|1531 L|221|468|-1190|90|10738|
|1531 R|249|542|-1417|44|12436|
|2053 L|389|709|-2121|-229|9785|
|2053 R|529|1028|-2455|-303|14188|

The comparison remainder changes sign; the original unique sum does not. A separate larger test fixed at the left endpoint B=b=5561, X=51541202 gives `(S5,V5,Q5,W5-Q5)=(-19217,5608,-12115,-1494)`, V5/L_b in `[13485,13486]*10^-6`. This is not an independent full-prefix census at that B. No fitted constant or limiting rate. For reference #1135 uses `E(B)=max_{1<=n<B}|M(n)|/sqrt(n)`. On any fixed diverging sequence B_j the eventual law `E(B_j^2)<=G_j E(B_j)^r` for fixed real 0<=r<2 and G_j>=1 with `log G_j/log B_j -> 0` has the critical every-epsilon/RH consumer; an independent supply of that law is missing. All measured sites start at `b^2>=B^2`, too late for the same rectangle's strict prefix. At the extra B=549,1024,1025,5561 controls the historical centered K_B is 3/2 and E(B)^2=1; neither is a new uniform bound.

**K. Reproducibility and uncertainty.** Deterministic Eratosthenes sign/square marking and literal multiplication were checked against independent C++ smallest-prime recurrence, per-integer divisors, squareful diagonals and the actual old convolution `2 sum_{i<B}mu(i)-sum_{i,j<B}mu(i)mu(j)floor(X/(ij))`. All 5,682,639 distinct (B,n) positions in the registered collars agreed on mu, largest prime, prime depth, D, T and `H0+T=mu`; the left endpoint is nested, not counted twice. The B=20,500 fixtures add 331 and 188251 positions. Separate trial-factor coprime rows and literal prime/cofactor tuples agree on Q5. As a compact reproduction of the core signed counts:

```text
for b <= i <= j, i*j <= X, mu(i)*mu(j) != 0:
    D[i*j] += 1; T[i*j] += (1 if i==j else 2)*mu(i)*mu(j)
for b*b <= n <= X with mu(n) != 0 and 5*Pplus(n) <= b:
    if D[n]==1: S5 += mu(n)
    if D[n]>=2: V5 += D[n]*mu(n)
```

Logarithms in the main tables use rational range reduction and 26 atanh terms with remainder `<=2w^53/(53(1-w^2)), 0<=w<=1/3`. The replay packet includes sources, site-class counts, both clock precision transcripts and compiler commands. Linux x86_64, CPython 3.12.14, NumPy 2.3.5, g++ 13.3 `-std=c++17 -O2 -Wall -Wextra -Werror`. The primary sieve costs O(X log log X) plus O(b^2) multiplication; secondary divisor enumeration and prefix convolution are independent. C++ full check 0.89s, coprime/area check 0.85s (observed, not a benchmark). No random seed, probabilistic primality, local Lean run or new CI dispatch.

**L. Specialist handoffs | LEDGER3-4, FINITE_COMPUTATION.**

- Architect / Referee: audit the restricted Mobius sum, uniformity and coprimality diagonal in LEDGER2, then PORT's independent coefficient. The six integer ledgers and the negative multiplicity witness are separate from those paper claims. No campaign switch requested.
- Owner / SLICE: at B=49,110,121, for X=B^2 and `e(t)=theta(t)-floor(t)`, the additive floor contribution `-floor(X/7)+2floor(X/10)-floor(X/11)` is respectively -81,-408,-494. Exact prime-log vectors reconstruct from psi only after removing proper prime powers; midpoint-to-inclusive additions to the combined prime-power expression are `(log 7)/2,0,(log 11)/2`. Not all square roots are covered by an almost-all statement.
- Wheel / WINDOW: J=10^12, a=1, s=21J/20, w=31/20. For q=95000011,110000017,130000001, take the three smallest primes in `[1.20J/q,1.22J/q]`: respectively (12637,12641,12647), (10937,10939,10949), (9239,9241,9257). Enumerating all 16 divisors of q times the three primes gives t=3,4,3 and `t(t-2)=3,8,3`; the middle triple product 1309936641007 enters alongside three `q*p_i`. This tests the cubic boundary, not a full three-prime area coefficient.
- Analytic / SQUARE: the old-pair certificate at H=78,96,114 was checked at `N=H^2,(H+1)^2,(H+2)^2,N-N^(7/8),N+N^(7/8)`. Signs in order: `--+-+`, `+---?`, `-+++?`; `?` denotes an inconclusive bound. At H=78 and the second successor square, the isolated new cofactor-two rows contribute `[-2115,-2114]*10^-10`, versus `[30231,30232]*10^-10` for the remaining change of the old-pair statistic. Not a sufficient condition for the physical Nyman norm.
- Referee / CLOCK and Lean: on H=126,132,...,180, only H=150 has an inner zero (cell (152,153)); only there does the prescribed derivative `S_H-2 gamma delta(H)` change sign between H and H+6. At `Y=N+floor(N^(7/8))` the fixed 16-block bound certifies an opposite endpoint sign at 138,144,150,180, the same sign at 126, and is inconclusive at the other five. So the crossing certificate is not selective. At 150, W(N) is `[18,19]*10^-8`, endpoint box `[-1073,-367]*10^-8`. At 174 the true endpoint is positive in `[4912,4913]*10^-12` despite an inconclusive box. Outward integer grids of 28 and 38 decimals gave identical decisions, with correctly rounded 80-digit logs padded two grid units and the alternating Euler-gamma tail after 512 controlled. No uniform zero law, full energy or eighth #1152 root.

**M-N. Ranked portfolio and resume.** (1) Promote the fixed-cofactor coprimality formula to independent paper review. (2) Test, not assume, this new conjecture: for infinitely many squarefree b, at `X=ceil(5b^2/3)` one has `2V5 <= (F5(c)+G5(c)) L_b`. If proved it refutes uniform suppression on this mask only. The single next experiment is to resolve V5 by compatible pairs of balanced splits: their four gcd intersections are pairwise coprime and all nonunit (distinct factors in [b,2b) cannot strictly divide one another). Keep the signed degree D, not `D(D-1)`; attack with the opposite five- and six-prime classes. (3) Retain complete strict-prefix growth as the unmet global condition; the physical VF history, Euler wheel compensation, NNS Hermitian rows, CORR4 and the Nyman full energy stay separate. Do not repeat the six prefixes or the 16-block scan without a new discriminator. Global half-step OPEN; RH OPEN; no verified ETA.

**Continuity and receipts.** Intake 08:11Z; main rechecked, reports directory inspected without a date cap. Previous reports intake `139c5523cbd3fb4dee537cb65acb3bcf26c34e59` to `7471a211745ecb39bccdcfdf28be12f6b72a010c`: 15 commits, 12 changed paths. Nov 20 TODAY=RECEIVED: Owner SLICE `4efb6209` (00:09 EST), Analytic SQUARE `ac32607e` (01:04), Wheel WINDOW `5e9b51ec` (02:05). Coordinator, previous Census, Referee and Lean TODAY=PENDING at intake; YESTERDAY=CARRY_FORWARD from Nov 19: PORT `b107495e` (23:09, mirrored), CLOCK `1093df2a` (19:00), ESCAPEMENT `e063ee0f` (20:13), PLATEAU/TWO-WITNESS `6231b482` (21:08). These supersede JET/HINGE/PHASELOCK/GATE/CROSS/LENS/RAMP where their scopes overlap. External inbox `7d63d434`: EXT-20261018-PNT-1 retains unit and p=R; EXT-20261014-5 is an all-root, not first-bad, claim. CONTINUITY_UNVERIFIED for abbreviated archival displays and the previously reported Nov 13-15 gaps only; not a substitute for the live sources.

Verified exact-head hosted steps: #1119 source `f629db1b`, raw `77ee8158`, run/job 42552018910/128949473700; #1135 envelope `9b25e34a`, RH bridge `02a88cad`, raw `ac6dc46b`, 43777334576/133006501690; #1152 raw `907105dd`, tree `726dae6e` identical to main, 44664507110/136050421713. #1149-51 are finite period/phase/profile results, #1152 has seven finite clipping roots; prior kernel receipt only propext, Classical.choice, Quot.sound. TWO-WITNESS has Coordinator paper acceptance only. No change to a branch other than this owned report on `agent-reports`. Opening verified by exact-commit readback at `61d7792ca0730951071d59f2bbdb74f55853e4b8`, blob `43c52a2195e73994c9ae3cd751eacb0d9f5a0f7e`, 2145 bytes. Final publication requires a separate exact-commit byte/hash readback, not this prospective note.
