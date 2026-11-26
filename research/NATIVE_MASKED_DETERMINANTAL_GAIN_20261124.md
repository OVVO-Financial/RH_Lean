# Native determinantal-divisor realization of the actual local gain

2026-11-24. Research continuation on #1201, under the strict exclusion policy.
Status: independent finite arithmetic lemma proved on paper and exact integer
diagnostics passed. Not Lean-verified and not a global signed-cost or RH proof.

## 1. An integral object, not an assigned gain field

Let A and w be integers with 0 <= w <= A. For each prime p choose a finite
set I_p of positive exponents, with p^i <= A for i in I_p. Only finitely many
are nonempty. The mask can be specified by independently computed arithmetic
conditions. Define an actual diagonal integer matrix

    D = diag(d_1,...,d_A),
    d_n = product_p p^(#{i in I_p : p^i divides n}).

Let Delta(A,w,I) be the gcd of all (A-w)-minors of D, with the empty minor
equal to 1. It is the actual determinantal divisor, not the target weighted
source assigned to a record field. Its exact valuation is

    v_p(Delta(A,w,I)) = sum_{i in I_p} max(floor(A/p^i)-w,0).       (1)

Proof: the nonzero minors are exactly the products over subsets of
A-w distinct diagonal entries. Their gcd has the minimum p-valuation.
The p-valuation of d_n is a nondecreasing function of v_p(n).
Remove the w integers with largest v_p(n), breaking ties in any way.
For every i simultaneously, this removes min(w,floor(A/p^i)) of the
multiples of p^i. The retained subset therefore achieves the lower bound
max(floor(A/p^i)-w,0) at every selected threshold. Every other retained
subset has at least that many multiples at each threshold. Summing gives
(1). The subset attaining the minimum may depend on p, as is permitted
for the valuation of a gcd; it is NOT asserted to be one subset attaining
all primewise minima.

Consequently

    log Delta(A,w,I) = sum_p log(p) sum_{i in I_p}
                            max(floor(A/p^i)-w,0).               (2)

The ordinary matrix diag(1,...,A) uses all exponents. The odd version
uses odd exponents only; then d_n uses ceil(v_p(n)/2) for the selected
primes. Arbitrary masks work as well, including nonconsecutive exponents
selected separately at each p. Thus the construction retains genuine
positive integer local indices, unlike the unimodular floor-wheel
operators whose determinant is one.

## 2. Apply to the literal native thick prime-power mask

Use the actual host in
[NativeDyadicHostPrimePowerWeights.lean](../RHLean/Analysis/AlpogeThin/NativeDyadicHostPrimePowerWeights.lean).
Its theorem nativeDyadicHost_fullASK_eq_oddClassSums_add_dCorrection gives
2 log(p) times the odd inert unramified prime-power site kernel and the
separate ramified d correction.

For a fixed actual (u,t,j), select the odd exponents i of unramified inert
p for which i*frob(p) belongs to the actual
alpogeNativeProjectionThickColours T2 u t, including the existing sharp
cutoff. See [AlpogeNativeSubgroupProjection.lean](../RHLean/Analysis/AlpogeNativeSubgroupProjection.lean).
The mask is determined by the same arithmetic host, not by the desired
estimate. It may depend on u,t,j. No claim that these masks are identical
is needed.

On the frozen thick width b, with b a positive integer and a >= b, use
A=floor(a), w=b. Each selected site contributes
2 log(p) max(a/p^i-b,0). Since p^i is an integer,
floor(a/p^i)=floor(A/p^i). The difference between the positive parts of
the continuous and floored expressions is nonnegative and less than one;
it vanishes whenever p^i>a/b. Thus the frozen thick source B satisfies

    0 <= B - 2 log Delta(A,b,I) <= 2 psi(floor(a/b)).             (3)

The bound uses the full von Mangoldt prime-power census, not a prime-only
count. If a selected exponent lies beyond A, it contributes zero to both
sides and is omitted from the matrix mask.

The native thick-freezing estimate handles deviations from b; (3) concerns
the already frozen width. Choosing integral b near the original exponential
width is a proposed parameter realization, not a proof that all other
original width/height/window conditions hold for that choice.

Averaging and summing (3) over the same actual top/lift indices and dividing
by Q=T*m*b*Delta_density/2 charges at most

    4 max_t psi(floor(a_t/b))/(b*Delta_density).

With a_t/b <= x+1 and the existing positive b and density estimates this
rounding cost is exponentially small up to polynomial factors. It is not
the missing critical estimate. This is a direct local arithmetic attachment
with a genuine integral object and a paid floor discrepancy.

## 3. The still-unpaid global comparison

Do NOT identify this determinantal divisor with the upstream LPprimeAt
restriction lattice or its Ga by definition. A positive local index is
not a bound on its global cost.

The actual remaining problem is to find a *same-object* global
determinantal/volume comparison with the original centered MAIN term,
retaining thin returns, the ramified correction, and all rank/height
costs. For this particular diagonal construction, taking any one minor
gives only a crude bound; for the ordinary diagonal, choosing the first
A-b coordinates gives log Delta <= log((A-b)!), at the wrong scale when
A is about bx and b is exponentially large. No square-root saving is
proved by (1)-(3).

A varying-width profile can be grouped by integer width and assigned
separate masked diagonals, but this does not automatically identify their
product with one unrestricted determinantal divisor or earn an affordable
global dimension. Nor can an arbitrary sequence of layer residual ranks
be interpreted as one p-primary module: such module ranks must be
nonincreasing with the layer index, whereas a change from a large width
to a small width can increase the residual. For example A=100, p=3,
w_1=33 and w_3=1 gives residual counts 0 and 2. This is a structural
warning for candidate constructions, not a counterexample to the actual
full geometry or to RH.

The next substantive proof is a global upper bound on independently
constructed minors/volumes with the signed center at the required scale.
If the construction cannot provide that, discard it rather than
introducing an assumed cost, synthetic height, or placeholder witness.
The native bound handoff is unchanged.

## 4. Diagnostics

Exact enumeration of all subsets defining nonzero minors checked 720
ordinary/odd selected-prime cases and another 360 arbitrary-mask cases
for A=1,...,12 and every 0<=w<=A. All 1080 checks matched (1).
For A=12,w=2 and all primes <=12 the ordinary gcd is 288 and the
odd-exponent gcd is 144. These tests verify finite examples only.

The accompanying diagnostic script reproduces these tests.
No external geometry declaration, imported terminal RH theorem, or
claim of a compiled Lean proof is introduced here.
