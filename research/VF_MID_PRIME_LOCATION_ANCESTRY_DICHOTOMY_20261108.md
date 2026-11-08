# Prime-location ancestry across the moving square-root wheel

2026-11-08. Source-faithful theorem attack, anchored in the genuine prime
sieve of RH_Lean. **No new RH, Mertens 3/4, Li-fan, spatial equidistribution
or uniform signed-owner bound is claimed.**

## 1. Correct scope of the user's asymptotic descent conjecture

The tiny R=4 example only refutes the literal universal transfer of exact
midpoint balance. It is NOT evidence against an asymptotic normalized
threshold or against a supercritical signed-square-block anti-clustering law.

The only viable strong claim is a quantitative, source-faithful scale rule:
if the original prime population of B_R has a SUPERCRITICAL location
imbalance, that imbalance must trigger a comparably normalized excessive
signed descendant or a terminal violation already controlled. Merely
finding some earlier prime divisor or some smaller square-root index
does not satisfy this quantifier.

## 2. Already-paid facts in the repo

* VF_MID_SQUARE_WHEEL_BACKLOG.lean proves in every open physical block
  B_R = (R^2,(R+1)^2), for R>=2:
  - every composite has some prime divisor <=R;
  - the full prefix wheel through R has exactly the genuine prime sites;
  - a partial wheel through S<=R includes all prime sites;
  - those partial survivor sets are nested and supply bounds.
* VF_MID_RECURSIVE_SCALE_DESCENT.lean proves strict drop of the relevant
  recursive child square-root index and a generic no-bad infinite-descent
  endgame. This proves termination, not inheritance of a supercritical
  same-source phase or prime-count event.
* VF_MID_FIRST_BAD_CORRELATION_DESCENT.lean proves a general selector for
  excessive signed rank components, conditional on actual terminal-sector
  payments; it does not supply location-bias payment.
* VF_MID_GLOBAL_PHASE_UNIFORMITY_BRIDGE.lean already proves the
  square-root half-phase / midpoint prime-population equality and its
  exact global telescope. VF_MID_FLOOR_LI_DISCRETE_BACKLOG.lean separately
  proves actual prime-count-minus-floor-Li accumulation.

## 3. New unconditional two-channel arithmetic descent

Let P_R be genuine primes in B_R, V_(S,R) the set of original sites
surviving all prime divisors <=S (the *genuine* partial wheel), and
L_(S,R)=V_(S,R)\P_R. For any position n, set sigma_R(n)=+1 in the first
half, -1 in the second half. Write C_R(E)=sum_(n in E) sigma_R(n).

The new source module proves, for every 2<=R and S<=R:

  P_R = V_(S,R) \ L_(S,R),
  C_R(P_R) = C_R(V_(S,R)) - C_R(L_(S,R)),           (1)
  |C_R(P_R)| <= |C_R(V_(S,R))|+|C_R(L_(S,R))|.   (2)

Unlike a triangle inequality on Mobius, this is an exact prime-
candidate/removed-composite occurrence-preserving split. It also proves

  |C_R(P_R)| > T + |C_R(V_(S,R))|
       ==> |C_R(L_(S,R))| > T.                    (3)

Every removed n has an ACTUAL prime factor q with S<q<=R, hence
floor(sqrt(q))<R. This establishes strict arithmetic ancestry for EVERY
new-removal site, uniformly in R. It does NOT establish that the q-th
historical prime block was itself spatially nonuniform, nor that the
newly removed sites can be regrouped without collisions or loss.

## 4. A TRUE asymptotic fixed-wheel theorem (elementary)

Let W be a fixed squarefree primorial (or any positive modulus) and
f_W(n)=1 if gcd(n,W)=1, else 0. For EVERY R, the two halves of B_R
contain R sites each. Write R=kW+t with 0<=t<W.

Since f_W is periodic with period W, each half contains exactly
k*phi(W) survivors from its k full periods. Only its t leftover sites
can distinguish the halves. Therefore

  |C_R(V_(S,R))| <= t < W  whenever W=W_S.         (4)

Consequently a genuinely supercritical location bias >W_S+T is
necessarily borne by the complete signed L_(S,R) owner response. If
W_S=o(R/log R), then the fixed-wheel spatial imbalance is negligible
compared with the typical P_R~R/log R, conditional on the usual PNT
asymptotic; this does not require a prime-independence assumption.

The period-splitting proof is elementary and all-scale. The new Lean
source's exact two-channel and divisor-witness statements are submitted
for kernel verification; formula (4) is mathematically proved in this
note but is NOT YET a named Lean theorem in this PR. Do not misreport
that status.

## 5. Arbitrarily large residue-class falsifier to *exact* inheritance

Take a moving square root R=6k+4, any integer k>=0. The 2-wheel is
perfectly balanced between the halves, since R is even. Introduce
the new, smaller prime divisor 3. Then R^2=4 (mod 6):

  left half starts at R^2+1 = 5 (mod 6);
  right half starts at R^2+R+1 = 3 (mod 6).

Both halves have R=6k+4 sites. After the 2x3-wheel (allowed residues
1 and 5 mod 6), the complete k cycles contribute 2k each.
The left remainder (5,0,1,2) has 2 survivors; the right remainder
(3,4,5,0) has only 1. Thus for *every* k,

  C_R(V_(2,R))=0,   C_R(V_(3,R))=+1.            (5)

This shows the noninheritance of PERFECT positional balance is not
a "small-number artifact"; a new sieve prime can change CRT phases at
arbitrarily large square roots. BUT the effect is bounded by 1 and
its relative size tends to zero. It does NOT refute the user's
proposed asymptotic SUPERCRITICAL inheritance statement.

## 6. Actual primes: no claim from the small R=4 example

An independent exact integer sieve (not probabilistic sampling)
reproduces the following actual genuine-prime half-block populations:

R | left | right | left minus right
---:|---:|---:|---:
2857 | 183 | 183 | 0
2858 | 174 | 174 | 0
2859 | 167 | 191 | -24
8524 | 467 | 467 | 0
8525 | 463 | 512 | -49
8911 | 503 | 503 | 0
8912 | 512 | 467 | +45

These show exact balance of one or two previous prime blocks can
precede a distinct current block even for ~1000 prime events. They
are finite observations; 49/975~5% is not a supercritical departure
by itself, and **none** proves failure of an asymptotic law.

Executable:
  python3 scripts/prime_location_ancestry_regression.py

The script also checks (5) for k up to 10,000 and |bias|<W for
various fixed W and roots. The proof of (5) is the preceding modular
argument, independent of the numerical range.

## 7. What the infinite descent still needs

The current exact descent is

  huge spatial bias at R
   => huge prefix-wheel bias OR huge signed later-owner location mass
   => *some* new actual prime owner q in (S,R] at smaller root.

This is NOT yet

  huge spatial bias at R => huge spatial bias at sqrt(q)<R.

The missing bridge must control how the complete signed location
mass of all later-owner fibers reassembles at child scales. Single
owner selection by a crude pigeonhole can pay a factor pi(R);
geometry alone has NO sign-preserving or norm-preserving inverse.
The source-integrity correction is essential: stripped child
cofactors can be prime, composite or squareful, and boundary
corrections can reverse a positional sign.

The new candidate quantitative lemma worth proving is a fixed
C_epsilon and a moving cutoff S(R) with W_S<<R^a, a<1, such that

  |C_R(L_(S(R),R))| <= C_epsilon R^a       (uniform all R),   (6)

or a rigorously signed *run/energy* version with original endpoints
and cross terms. Together with (4) this gives a local prime-phase
bound. For Mertens 3/4 or Li fan control, additional bridges from
positional bias to genuine prime count and signed Mobius cofactor
energy are still required: neither is automatically supplied
by location uniformity.

No RH, unconditional 3/4 bound, nonescape theorem, nor all-scale
inequality (6) is currently proved.
