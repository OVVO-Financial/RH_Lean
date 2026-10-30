# Owner contraction and the complete signed return: proof attempt and exact obstruction

2026-10-30. Original source only. The user's requested fixed positive gain after the COMPLETE physical signed return is **NOT PROVED** here. This work proves a positive reciprocal-exponent margin and exposes, on the actual arithmetic graph, why it cannot simply be inverted. Structural/finite theorems count as certified only after their exact-head Lean checks pass. No RH or improved Mertens exponent is claimed.

## 1. Exact original source and intended bootstrap

For endpoint X, the repository's exact post-root identity is

    M(X)^2 = Family(X) + 2[T(X)+A(X)] + D(X),
    0<=D(X)<=X,  T(X)<=0,
    Family(X)=sum_(sqrt X<p<=X, p prime) M(floor(X/p))^2.

The parent advantage A is the original child-multiplicity-weighted Div-minus-Co sum, not a model population. Its signed terminal partner T must be retained when helpful. Packing gives Family<=X*K_X with K_X=max_(1<=t<=sqrt X) M(t)^2/t. Under an incoming power beta>1/2 this is O_epsilon(X^(beta+1/2+epsilon)).

A NEW theorem of the form

    T(X)+A(X) <= C_epsilon X^(1+epsilon) K_X^(2-sigma)

for one fixed sigma>0 would yield the desired exponent response. That statement is not assumed or proved by the files in this PR. It is the arithmetic signed-return obligation. The local reciprocal margin tau below is NOT sigma.

## 2. Positive reciprocal exponent slack: an unconditional theorem

Let k_X(u,p) be the ACTUAL multiplicity of original recursive children with parent u and least separating prime p. Existing proved arithmetic gives k<=2 and

    S_(X,u)(2)=sum_p k_X(u,p)/p^2 <=79/81.

Set B=2*sum_(n>=0) n^(-3/2), a finite real number. For 0<=t<=1 weighted AM-GM gives uniformly

    S_(X,u)(2-t/2) <=(1-t)S_(X,u)(2)+t*S_(X,u)(3/2)
                  <=(1-t)*79/81+t*B.

Choose t=1/[162(B+1)], tau=t/2. Then 0<tau<1/2 and

    S_(X,u)(2-tau)<=53/54<1.

The theorem has quantifier order EXISTS tau>0 FOR ALL X,parent. There is no imported 7/8 premise, no conjectural multiplicity bound and no source substitution. This proves an actual open interval of weighted contraction. It does not identify a physical unweighted gain.

## 3. The exact signed aggregate uses a different coefficient

With reciprocal amplitude a(m,n)=mu(m)mu(n)/(mn), each actual child obeys

    a(child)=-a(parent)/p.

Consequently the signed sum over ALL admitted children of one parent is

    sum_children a(child)=-a(parent)*sum_p k_X(parent,p)/p.

Its square is

    |a(parent)|^2 * (sum_p k/p)^2,

whereas the existing contraction controls

    sum_children |a(child)|^2=|a(parent)|^2*sum_p k/p^2.

These are different quantities. Children of the same parent have one common sign; their cross terms reinforce rather than cancel. The new Lean module proves this identity, the full square/diagonal/cross expansion, and the exact physical inverse-weight identity

    (mn)*a(m,n)=mu(m)mu(n).

Thus undoing the reciprocal weights exactly undoes the local prime suppression. Any global gain must come from signed interactions between different parents and the retained terminal population, or from another independently proved arithmetic restriction.

## 4. Genuine arithmetic witness, not an arbitrary operator

At X=35, parent (1,7), the ENTIRE actual recursive child fibre is

    (1,14),(1,21),(1,35),(2,7),(3,7),(5,7).

Their owners are respectively 2,3,5,2,3,5. All six children are in the original physical remainder: they are coprime pairs, so no common post-root prime removes them. Their parents are exactly (1,7). Chronology forces every possible owner below the next parent owner 7, so no other prime is admissible.

The parent amplitude is -1/7 and its energy is 1/49. Exact values are:

    sum child diagonal energies =361/22050;
    diagonal/parent energy ratio=361/450<1;
    signed reciprocal child sum=31/105;
    coherent-square/parent-energy ratio=961/225>4;
    unweighted signed child mass=6 (parent raw weight=-1).

The support proof uses chronology and the two-child theorem, not enumeration of an artificial sign matrix. Ground prime faces and Mobius values are checked by the kernel. These statements refute a per-parent signed return contraction. They do not refute an all-parent cancellation theorem.

The same fibre persists for every endpoint X>=35: all its children remain admitted and coprime, and chronology still restricts owners to 2,3,5. Thus the local problem is not cured merely by moving the starting threshold. The PR's explicit numerical Lean theorem is stated at X=35; this last all-X support extension is its mathematical consequence and is not separately exported as a Lean declaration.

## 5. A second obstruction at the imported baseline weight

A weighting a_beta(m,n)=mu(m)mu(n)/(mn)^beta gives local child-energy factor p^(-2beta). At beta=7/8, the same legal fibre already satisfies

    sum_p k/p^(7/4)>=2(2^(-7/4)+3^(-7/4)+5^(-7/4))>1.

The strict bound is certified without floating point using

    2^(-7/4)>19/64,
    3^(-7/4)>7/48,
    5^(-7/4)>1/17,
    2(19/64+7/48+1/17)=1637/1632>1.

Each lower bound follows by raising to the fourth power and checking r^4*p^7<1. These are exact rational certificates. A small slack below reciprocal exponent 2 therefore does not already provide contraction at reciprocal exponent 7/4, much less the original unweighted signed statistic.

This is a scope correction to the preceding informal suggestion: positive local tau is real, but it is not a demonstrated net exponent sigma after return.

## 6. Whole-source tests keep terminal and cross-parent cancellation

scripts/owner_signed_return_audit.py reconstructs the actual source using an integer Mobius sieve, least separating prime, all original child fibres and the post-root family subtraction. No random signs are inserted. For every tested endpoint it verifies

    M^2=Family+D+2(T+A).

Selected exact endpoint results (X, not square-root R):

|X|M(X)|Family|D|T|A|T+A|
|---:|---:|---:|---:|---:|---:|---:|
|13|-3|3|4|-9|10|1|
|35|-1|9|8|-27|19|-8|
|71|-3|17|14|-56|45|-11|
|127|-2|30|22|-99|75|-24|
|317|-4|75|49|-255|201|-54|
|1027|-3|217|156|-873|691|-182|

The positive value at X=13 rules out declaring the entire remainder always nonpositive. The other values show why terminal compensation should NOT be removed before the next estimate. These computations are regression/falsification, not an asymptotic proof.

## 7. The first unresolved original-source inequality

After the exact return, the object is STILL

    R(X)=T(X)+sum_parent k_X(parent)*[Div(parent)-Co(parent)].

The within-parent diagonal contraction is insufficient. A successful next theorem must control cancellation among different parents, jointly with T and their physical masks, uniformly over all required endpoints. One cannot assume that exact inequality as a theorem input and describe the resulting conditional closure as a proof of positive saving.

No conclusion here says the global target is false or that the RH_Lean approach cannot succeed. It pinpoints a false shortcut and proves the positive weighted result that genuinely follows from the existing arithmetic contraction. The complete global sigma>0 remains a separate, unproved obligation.

## 8. Verification boundary

- OWNER_RECIPROCAL_EXPONENT_SLACK_20261030.lean: actual uniform weighted exponent margin.
- OWNER_COMPLETE_SIGNED_RETURN_20261030.lean: source-exact coherent return, inverse weights, signed Gram, complete six-child fibre and exact expansion witness.
- OWNER_BASELINE_WEIGHT_WITNESS_20261030.lean: original local energy-congestion obstruction at 7/4 using exact rational fourth powers.

Dedicated CI uses pinned Lean 4.34.1, warnings fatal, exact theorem type checks, standard logical axioms only, no sorry/admit/project axioms and no native_decide. Mathematical statements in this note outside those declarations remain paper arguments, not automatically certified by structural CI. No merge or proof-status promotion is authorized by this draft.
