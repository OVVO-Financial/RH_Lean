# RH_Lean Prime Census Laboratory - 2026-10-22

**Status:** COMPLETED  
**Run:** 2026-10-22T01:51-04:00 scheduled invocation  
**Canonical objective:** `VFCanonicalSquareVonKochStatement` remains OPEN  
**Campaign status:** `INCOMPLETE; NO INDEPENDENT 7/8 PROOF`  
**Evidence:** `FINITE_COMPUTATION` (two independent implementations), `REFUTED` (uniform sign from raw quotient aliases), `NO_NEW_RESULT` (no new all-scale bound)

## A. Bottom line

Today's Wheel claim `20261022-wheel-1` proves that literal selected-ideal subset products are injective and that, after quotienting to the class seen by a row, the compensation-weight cross phase of a colliding pair is `(-1)^|symmDiff(J,L)|`. I instantiated the first source-legal quotient layer exactly and asked whether odd aliases themselves provide a one-sided moment contraction.

They do not.

For four disjoint slots of primary Eisenstein prime generators with rational norms in

```text
[50,100), [100,200), [200,400), [400,800),
```

and each rational-principal quotient ideal `(m)`, `m in {5,7,11,13,17,19}`, I enumerated all 384,000 selected tuples, all 16 Gaussian subsets, and every raw quotient fiber in `O/(m)`. The six moduli therefore contribute 2,304,000 tuples. Every modulus contains all four behaviors: collision-free, even-only aliases, odd-only aliases, and mixed-parity aliases.

For a tuple `p=(p_i)` define `Q_J=prod_(i in J) N(p_i)` and the coefficient-only energies

```text
E_diag = sum_J Q_J^(-3),
E_quot = sum_x (sum_{J: rho(p_J)=x} (-1)^|J| Q_J^(-3/2))^2.
```

Raw quotient equality makes the omitted Hecke complement-character phase common within each fiber, so this is exactly the original Gaussian subset coefficient contribution after quotient aggregation, but before slot windows, log phases and the integrated physical-row core. For every tested modulus there are tuples with `E_quot/E_diag < 1` and tuples with `E_quot/E_diag > 1`.

This is claim **`20261022-census-1`**:

> Neither existence nor abundance of odd raw quotient aliases forces a coefficient-level contraction after all even and odd alias cross terms are restored. The reverse one-sided expansion claim is also false.

Classification: **`FINITE_COMPUTATION / REFUTED`**. This refutes a local deterministic shortcut, not a weighted moving-conductor theorem. It does not include the subset-dependent physical core and does not bound the OAI detector.

## B. Authority and continuity

Final pre-publication refresh used:

- `main@66af9b34c082485872815ece9a7721606381c07f`;
- `AGENTS.md` blob `20bff52d6784c17d4a7d6ac731f4a71c2bdad8a6`;
- `CURRENT_PROOF_CONTRACT.md` blob `2fa9931dcdc1fc8a816aefb8aa348db12ee9a384`;
- native 7/8 replication protocol blob `53194dc3ae106be363bc22cf85a88bac4a3b2e6e`;
- dynamic protocol blob `bd1189617c069565a881c2a5c5dbd9a138bc48c1`;
- external handoffs blob `038018145c0fddb2f6306c0712373adf9cd1ea52`.

Original pinned OAI source `openai/math@1581d4cbdd69a0faf34b2089614fe2a814316a6a` was read directly:

- `Hecke/Family.lean` blob `3d87da47cd57f0a4f11859c654e3e3202a519100` defines `Character`, `elementCoeff`, and the quotient residue character;
- `Hecke/Coordinates.lean` blob `afab18be7bcb5a3a9590457f285a3b286553ef16` proves the coordinate-to-quotient map;
- `Detector/GaussianCompensation.lean` blob `27cc33df0202e1693b98d38bc9032c7c3de475a4` defines the literal `(-1)^|J| Q_J^(-3/2)` coefficient;
- `Detector/GaussianCommon.lean` blob `ab1e3bff726fd851a0091cc43ac98a765881f3ad` retains all subsets, slot tuples, row tests and Gaussian integrals.

Native ideal-coordinate reconstruction on main is `research/VF_919_NATIVE_SEXTIC_IDEAL_FIBER_20261019.lean`, blob `cc99bbb2d02b700ff9cf2e555861208430f42acc`. Draft #1003 head `955cfaf098aa23d4a9e9bea8f910ffa481521b59`, source blob `bfdb1070131743001404428579e3d69336dd70d9`, preserves the same subset coefficient with an opaque complete physical core. Draft #1004 remains open at `f5496fdf303434420f4950c57ad50daeed9bd295`; today's Wheel reports its two mandatory original-type gates failed, so it is not compiled bridge evidence.

At intake and final refresh, today's directory contained only Wheel report blob `67d6d669f279a0ecf843b0f5ebed47f7a227d335`, claim `20261022-wheel-1`. Coordinator, Owner, Analytic, Referee and Lean are `TODAY=PENDING`. The 2026-10-21 reports were read at blobs `fb11676896cefe49fc25a5b03b16e278085cc8a5`, `f2dbb2c646afce789071902fcb5e9f05c4bed8b2`, `7583f9062b783777af0054d29e0a81802bdf99d6`, `b7ea2642bb7713e8a1685dc77c5a3b3b0f1cc800`, `e6ef7fa0ebffeea4643b9e892591156d6cd0c1fb`, and `6c0d5af5ad0b00608643513585bd6a8c59207098`; they are `YESTERDAY=CARRY_FORWARD`, not current executions.

## C. Mathematical question and preregistration

**Mystery.** Wheel identified odd symmetric-difference quotient aliases as the only coefficient-layer aliases capable of destructive aggregation. Does the genuine selected-prime incidence force enough odd aliases to make the quotient-aggregated coefficient energy one-sided?

**H1 (parity obstruction).** Actual primary selected primes admit a parity grading, so odd raw quotient aliases do not occur.

**H2 (local compensation).** Odd aliases occur and dominate all constructive even aliases, giving `E_quot <= E_diag` for every tuple.

**H3 (sign-changing incidence).** Odd and even fibers both occur; their restored cross terms give both contraction and expansion, so only a weighted restricted-kernel or nonlocal theorem can pay the moment.

**Discriminator fixed before execution.** Exhaust the four stated disjoint slots for six stated prime moduli. Count exact unordered colliding pairs by parity and compute `E_quot/E_diag`. One odd collision refutes H1; one ratio above one refutes H2; examples on both sides for all moduli support H3 without proving an asymptotic statement.

## D. Exact carrier

Write `O=Z[omega]`, `omega^2+omega+1=0`. A selected primary generator is an integer pair `(a,b)` with

```text
N(a+b*omega)=a^2-a*b+b^2=p,
a == 1 (mod 3), b == 0 (mod 3), p == 1 (mod 3) prime.
```

Each split rational prime contributes its two distinct primary generators; equal rational norms are not deduplicated. The four slot cardinalities are `10,20,32,60`. Tuple products use the exact law

```text
(a,b)*(c,d) = (a*c-b*d, a*d+b*c-b*d).
```

Reduction coordinatewise modulo `m` is precisely multiplication in `O/(m)`. Tuples containing norm `m` are excluded, so every selected generator is a unit at the rational prime modulus. Raw quotient equality is stronger than equality under one character: it forces equal `elementCoeff` for every Hecke residue character with that modulus. Character-kernel aliases not visible in raw equality are intentionally omitted; thus the census does not overstate alias incidence.

Every subset occurrence is retained. No physical owner is multiplied by the size of a norm fiber, and no window, row, zero branch, principal signal, dyadic index or height integral is claimed to be present.

## E. Results

Exact structural counts agreed between independent Python and C++ reconstructions:

| m | no alias | even only | odd only | mixed | even pairs | odd pairs | min ratio | max ratio |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 5 | 39,136 | 125,960 | 128,424 | 90,480 | 811,208 | 991,984 | 0.999221364974038 | 1.000004395489539 |
| 7 | 127,586 | 106,348 | 108,594 | 41,472 | 534,832 | 550,640 | 0.999768468011980 | 1.000003575774371 |
| 11 | 283,118 | 50,866 | 45,340 | 4,676 | 154,408 | 104,872 | 0.999999998780693 | 1.000001498456070 |
| 13 | 313,108 | 30,332 | 38,372 | 2,188 | 74,510 | 87,952 | 0.999999998262447 | 1.000000379724467 |
| 17 | 342,982 | 19,134 | 21,424 | 460 | 47,868 | 44,544 | 0.999999999131022 | 1.000002863435788 |
| 19 | 348,798 | 17,354 | 17,310 | 538 | 46,290 | 37,576 | 0.999999998641247 | 1.000002165653967 |

The smallest hand-checkable odd-alias certificate in the fixed enumeration is modulo 5:

```text
tuple = (-5,-9; N=61), (-11,-9; N=103),
        (-14,-15; N=211), (-23,-15; N=409).
```

The third generator is `(-14,-15) == (1,0) mod 5`. Therefore subsets `J={0}` and `L={0,2}` have the same quotient product and odd symmetric difference `{2}`. This directly refutes H1.

The most contracting modulo-5 tuple has ratio

```text
0.9992213649740379753606452649149399785997620129901...
```

while an even-only tuple

```text
(7,-3;79), (7,12;109), (-5,12;229), (-23,-18;439)
```

has ratio

```text
1.0000043954895394122796366413146566473483828428890...
```

and therefore refutes H2. All six moduli independently show both signs. The weakest reported sign margin is about `8.69e-10`, still more than six orders above ordinary double roundoff at unit scale. Decimal recomputation at 50 and 100 digits agreed through at least 42 leading digits for every extremum. These are high-precision diagnostics, not interval certificates; the exact alias counts and collision certificates use integers only.

## F. Independent verification and reproducibility

Python and C++ independently implement primality, primary-generator enumeration, Eisenstein multiplication, quotient reduction, subset fibers and parity counts. C++ uses `long double` for the energy ratio; Python uses binary64 for the full census and a separate 100-digit `Decimal` recomputation of all extrema.

```sh
python alias_parity_census.py > alias_parity_python.json
g++ -O3 -std=c++17 -Wall -Wextra -Werror \
  alias_parity_census.cpp -o alias_parity_census_cpp
./alias_parity_census_cpp > alias_parity_cpp.txt
python alias_parity_precision_check.py > alias_parity_precision.txt
```

Environment: CPython 3.12.14; GCC 13.3.0; x86_64. The transparent Python pass took approximately 45 seconds and the optimized C++ pass approximately 3 seconds in the scheduled container.

Source SHA-256:

```text
Python census   699325a7b336d41e4177f6b44b17de6a2f763352ffd2764f2a0e6bda396287e2
C++ census      5c444e1e7e96f4165d7dfd4f5e386aadc27f8016866fe482a17452c5532a655c
precision check cd2b95a70df2a58235340d6edc5c0e542aac8a20651c880e27ca8594b92ea57d
```

Output SHA-256:

```text
Python JSON 2a25c07601dc452b53b82caab84d401203e24ca5b468a738a96ff8b1db512d14
C++ text   7ac3a01f0424fd44b063481d612c8a5f2910742b75d15a96206268a0e185d6bb
precision  b7c4f1fa1c2e56ca7fc3d9450c274124db6ca122176138ff195bad7a16868eba
```

The exact-count comparison asserted equality for `tuples`, all four tuple classes, and both parity-pair totals at every modulus. Canonical Python payload hash (before adding its own hash field): `eca5cdff77c046457970d9e302fc9bfbec5fe96fe3f7338684211dbc22d52654`.

## G. Proof impact and limits

1. Claim `20261022-wheel-1` is computationally instantiated on genuine Eisenstein quotient multiplication: odd destructive aliases really occur; they are not merely abstract finite-group possibilities.
2. Odd-alias existence, count, or density is not a signed moment payment. Even aliases and unequal `Q_J^(-3/2)` magnitudes restore either sign even on the coefficient-only carrier.
3. The correct next analytic object is a weighted restricted four-point kernel split by actual quotient fiber and parity, with slot windows, row-dependent physical core, zero branches and cross-height terms inside the same sum. A theorem on the odd sector alone is incomplete.
4. Raw quotient equality is conservative. A fixed character may introduce additional kernel aliases; those must be enumerated coefficientwise on the actual moving row rather than inferred from this table.
5. No Stage I 11/12 comparison, Stage III inverse/plain moment, native independent 7/8 theorem, original #915 payment, canonical VF estimate, or RH result follows.

Evidence status for the precise finite scope is **`FINITE_COMPUTATION`**. The universal coefficient-level sign claims H1 and H2 are **`REFUTED`** within the exact carrier above. No all-scale theorem is asserted.

## H. Continuation checkpoint

Do not enlarge the raw-modulus table unchanged. The next nonduplicate experiment is to extract one actual `DetectorPlainStateDictionary` moving row and its exact character kernel, then attach to every `(u,J,p,row,j,t)` atom:

1. raw quotient fiber and character-kernel fiber;
2. odd/even symmetric-difference sector;
3. `compensationSubsetWeight`, slot windows and log phases;
4. `physicalRowWeight * correctedCompletedT * gaussianJointDensity`;
5. `p|u` zero/one-active branch and principal restoration.

Recombine the complete complex source before taking its norm and verify it independently against the upstream subset sum. The decisive falsifier for a proposed local saving is a legal weighted row whose complete even-plus-odd restricted-kernel defect has the opposite sign. The needed theorem is a uniform weighted bound across moving conductors/heights, not a pointwise alias statistic.

No RH proof claim.

## I. Publication verification

The initial report was created on `agent-reports` by commit `9660b880e74b45f70de2275fef7c7a7db5fea48b`. Immediate readback returned blob `8244a0945498207203ec8aaf3996045dea0517dc`, 12,737 characters, `COMPLETED` status and claim ID `20261022-census-1`. This verifies publication only; it does not promote the finite computation to a uniform theorem. No main source, PR, review, workflow, merge, schedule or permission state was changed.
