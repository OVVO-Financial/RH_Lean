# Three-slot Walsh transition route

Status: research note for the branch `agent/three-slot-walsh-transition`.

This note records the elementary three-slot state model suggested by the exact four-slot Möbius cell and connects it to the existing square-block and prime-wheel recovery architecture. It deliberately separates exact identities from the open quantitative estimate.

## 1. The physical three-slot state

For a complete four-cell indexed by `k`, write

```math
A_k=(a_k,b_k,c_k)
=(\mu(4k+1),\mu(4k+2),\mu(4k+3)).
```

The fourth value is identically zero because `4k+4` is divisible by `4`. The existing theorem `moebius_four_mul_add_two` gives

```math
b_k=-\mu(2k+1).
```

Therefore the four-cell scalar is exactly

```math
C_k=a_k+b_k+c_k.
```

At a complete four-cell endpoint,

```math
M(4K)=\sum_{k<K} C_k.
```

This is the first important simplification: the Mertens observable is linear in the three slot coordinates.

## 2. The eight nonzero states and their Walsh basis

On cells where all three coordinates are nonzero, the state lies in

```math
\{\pm1\}^3.
```

The seven nonconstant Walsh characters are

```math
a,\quad b,\quad c,\quad ab,\quad ac,\quad bc,\quad abc.
```

The constant character is the population.

The Mertens cell observable

```math
a+b+c
```

lies entirely in the degree-one Walsh subspace

```math
\operatorname{span}\{a,b,c\}.
```

Hence full eight-state equidistribution is stronger than the RH target. In particular, the empirical `abc` mode is a useful diagnostic of complete state mixing, but it is not required in the linear Mertens observable.

This matters strategically. A square-root theorem for all seven modes would include square-root cancellation for the consecutive three-point product

```math
\sum_k \mu(4k+1)\mu(4k+2)\mu(4k+3),
```

which is a much stronger correlation target than is needed here. The RH-directed theorem should first target the three degree-one modes and their exact smooth-core correction.

## 3. Prime 2 is an exact middle-coordinate flip

The exact cell theorem gives

```math
(\mu(4k+1),\mu(4k+2),\mu(4k+3))
=(\mu(4k+1),-\mu(2k+1),\mu(4k+3)).
```

Thus prime `2` acts by

```math
F_b(a,b,c)=(a,-b,c).
```

On Walsh characters its eigenvalues are

```text
a    +1
b    -1
c    +1
ab   -1
ac   +1
bc   -1
abc  -1
```

This is an exact involution, not a probabilistic statement.

## 4. Exact odd-prime local transition on the squarefree-supported cube

Let `p` be an odd prime. Consider the three linear forms

```math
L_1(k)=4k+1,\qquad L_2(k)=4k+2,\qquad L_3(k)=4k+3.
```

Modulo `p`, each equation `p | L_j(k)` has exactly one residue class, and the three classes are distinct. Modulo `p^2`, each equation `p^2 | L_j(k)` also has exactly one residue class.

After deleting the three square-collision residues modulo `p^2`, there are exactly

```math
p^2-3
```

admissible residues. Among them:

```math
p(p-3)
```

residues have no `p` hit in the three slots, and for each coordinate there are exactly

```math
p-1
```

first-power hits that flip that coordinate.

Therefore the normalized local transition operator on the eight nonzero states is

```math
T_p=\alpha_p I+\beta_p(F_a+F_b+F_c),
```

where

```math
\alpha_p=\frac{p(p-3)}{p^2-3},
\qquad
\beta_p=\frac{p-1}{p^2-3}.
```

Because the coordinate flips commute, the Walsh characters diagonalize `T_p`. A Walsh character of degree `r` has eigenvalue

```math
\boxed{
\lambda_{p,r}
=1-\frac{2r(p-1)}{p^2-3}.
}
```

The multiplicities are `1,3,3,1` for degrees `0,1,2,3`.

For `p=3`, the identity part vanishes and exactly one coordinate is active in every cell, agreeing with `prime_three_active_slot_cycle`.

## 5. Complete CRT periods versus physical prefixes

For a complete CRT period over odd prime squares, the local transition measures convolve exactly. Hence a degree-`r` normalized Walsh bias is multiplied by

```math
\prod_{3\le p\le y}\lambda_{p,r}.
```

This gives a clean exact full-period spectral model.

However, this by itself is not an RH-scale theorem. The prime-square CRT period grows far faster than the physical prefix. The open problem is the incomplete-period frontier.

This is the same physical-cutoff obstruction already isolated elsewhere in the repository.

## 6. Numerical physical-cutoff experiment at x = 10^7

There are

```text
K = 2,500,000
```

complete four-cells through `x=10^7`.

For the odd-prime-square CRT period,

```math
Q_{11}=3^2 5^2 7^2 11^2=1,334,025<K,
```

while

```math
Q_{13}=Q_{11}13^2=225,450,225>K.
```

Thus prime `13` is the first point where the full local period no longer fits inside the physical cell prefix.

The measured partial-wheel Walsh biases track the exact full-period eigenvalue products extremely closely through this transition.

| last odd prime | theory degree 1 | observed max degree 1 | theory degree 2 | observed max degree 2 | theory degree 3 | observed degree 3 |
|---:|---:|---:|---:|---:|---:|---:|
| 11 | 0.130211 | 0.130214 | -0.028740 | 0.028751 | 0.009714 | 0.009723 |
| 13 | 0.111386 | 0.111437 | -0.020430 | 0.020448 | 0.005501 | 0.005534 |
| 19 | 0.088975 | 0.089101 | -0.012669 | 0.012856 | 0.002552 | 0.002642 |
| 3163 | 0.014864 | 0.035579 | -0.000338 | 0.002898 | 0.0000104 | 0.000581 |

The deviation at large wheel depth is therefore a physical-prefix effect, not a failure of the local cube transition law.

This is a strong indication that the theorem should be formulated as a signed incomplete-CRT or square-block frontier estimate rather than as an abstract stationary Markov-chain spectral gap.

## 7. The initial minus seed has exact square-root semantics

The initial state `(-,-,-)` is not merely a heuristic seed.

`PrimeWheelMobiusRecovery.lean` already proves that when the prime coordinates cover every prime through the square-root cutoff, a squarefree nonsmooth integer has exactly one unresolved large prime. Consequently the seeded prime comb, which begins at `-1`, already has the correct Möbius sign on every nonsmooth squarefree site.

On a fully smooth squarefree site, the anticipated large prime is absent, so the seed has the opposite sign. The existing smooth-core correction flips exactly those sites:

```math
\text{corrected}=\text{raw}-2\,\text{smoothCore}.
```

Squareful sites are killed exactly.

Thus the elementary slot process has three layers:

```text
initial minus seed
  -> small-prime coordinate flips and square kills
  -> smooth-core correction
  -> exact Möbius value.
```

## 8. x = 10^7 raw versus smooth-core cancellation

Using every prime through `sqrt(10^7)`, the three seeded slot sums over the 2.5 million cells are

```math
(98,983,\,-101,628,\,98,288).
```

The corresponding smooth-core sums are

```math
(49,262,\,-51,048,\,49,089).
```

After the exact correction `raw - 2 smoothCore`, the three coordinate sums become

```math
(459,\,468,\,110).
```

Therefore the total cell sum is

```math
95,643-2(47,303)=1,037.
```

This is the actual Möbius prefix at the complete four-cell endpoint.

The decisive empirical cancellation is therefore not primarily the disappearance of the `abc` mode. It is the near annihilation of the seeded degree-one bias by twice the smooth-core degree-one bias.

## 9. The theorem target suggested by the data

For slot `j`, define a seeded prime-wheel prefix `R_j` and its smooth-core prefix `H_j` on the corresponding linear form. At square-root coverage the exact pointwise recovery gives

```math
M(4K)=\sum_{j=1}^3 \bigl(R_j(K)-2H_j(K)\bigr).
```

The direct RH-scale target is therefore

```math
\boxed{
\left|
\sum_{j=1}^3 \bigl(R_j(K)-2H_j(K)\bigr)
\right|
\ll_\varepsilon K^{1/2+\varepsilon}.
}
```

A stronger but still relevant target is the coordinatewise estimate

```math
|R_j(K)-2H_j(K)|\ll_\varepsilon K^{1/2+\varepsilon}.
```

This target satisfies the two project acceptance criteria:

1. it is expressed directly in the square-block and square-root prime-wheel recovery architecture;
2. a square-root estimate contracts the generalized proven PNT route to the RH scale through the already formalized Mertens and zeta bridges.

## 10. Proposed exact Lean layer before any analytic claim

The first Lean change should remain purely exact and dependency-bounded.

Suggested module:

```text
RHLean/Arithmetic/ThreeSlotWalshTransition.lean
```

Suggested contents:

1. a three-slot state structure;
2. `activeTriple` and the odd-source triple;
3. exact prime-2 middle flip from `moebius_four_mul_add_two`;
4. the seven Walsh monomials and their prime-2 eigenvalue identities;
5. the linear observable `a+b+c` and its exact equality with `fourSlotCellSum`;
6. a seeded three-slot field built from `seededPrimeComb`;
7. a smooth-core three-slot field;
8. exact square-root recovery of each corrected coordinate from `correctedPrimeWheelSite_eq_moebius`.

A second module can formalize the odd-prime residue counts and the rational local eigenvalue formula. No spectral contraction theorem should be claimed until the physical-prefix frontier is controlled.

## 11. Guardrails

- Do not require square-root control of all seven Walsh modes. The degree-three mode is a stronger Chowla-type correlation and is not present in the Mertens linear observable.
- Do not model successive cells as an autonomous Markov chain. The arithmetic state retains residue information that is lost by the eight-state marginal.
- Do not replace the raw-minus-twice-smooth combination by separate absolute estimates.
- Do not lose the square-root coverage interpretation of the initial minus seed.
- Do not claim the complete-period eigenvalue product controls an incomplete physical prefix without a frontier theorem.

## 12. Current working conjecture

The three-slot model suggests that the main quantitative theorem should be a degree-one Euler-CRT coherence estimate for the joint seeded and smooth-core field on square-block prefixes.

The exact local cube walk explains the interior cancellation. The remaining bias is a signed physical-prefix frontier effect. The smooth-core correction then removes the false unresolved-prime seed on fully resolved sites.

The intended chain is therefore

```text
three-slot prime transitions
  -> exact degree-one Walsh diagonalization
  -> incomplete-CRT square-block frontier control
  -> raw-minus-twice-smooth degree-one cancellation
  -> Mertens square-root bound
  -> existing zeta continuation and functional-equation route
  -> RH.
```
