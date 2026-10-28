# OAI 7/8 -> genuine Euler three-part square-shell localization

Date: 2026-10-28. Goal: transfer ORIGINAL OpenAI's analytic cancellation mechanism, preserving actual moving Euler prime populations, rather than infer a local moment from a global theorem. This audit identifies exactly which source and moment statements transfer, and where the analytic proof remains open.

## 1. Original exact sharp coefficient / source

For R>=4 put X_R=R^2-1. The original native quadratic norm coefficient satisfies, at every integer,

    mu_Z(n) = sum_(md=n) a_F(m)*chi_{-3}(d).

The actual finite original sharp paired square-source is

    T_R = sum_(m,d: R^2<=md<(R+1)^2) a_F(m)*chi_{-3}(d)
        = M(X_(R+1))-M(X_R) = Delta_R.

All norm-fiber, split/inert/ramified, squareful-zero, and within-site mixed terms are retained. Its physical indicator is imposed BEFORE reassembling the norm fibers and BEFORE squaring.

The new warning-fatal Lean file OAI_PAIRED_SHARP_EULER_SQUARE_LOCALIZATION_20261028.lean transfers this source EXACTLY to the user's three moving Euler prime-admission fluxes,

    T_R = Delta E_R + Delta C_R - Delta P_R,

where E is low-prime smooth mass, C the genuine high-prime composite response and P counts newly admitted prime singletons. The analogous three *site-location* flux is also proved, retaining the X/2 moving gate transfers (and composites in the upper half). It proves the exact moment identity

    E_sharp(H)=sum_(H<=R<2H)|T_R|^2
              =sum_(H<=R<2H) Delta_R^2
              =native Euler 3-component six-term signed Gram.

This is a genuine source-level equality; it does NOT identify the sharp window with OAI's selected completed cubic-theta probe.

## 2. Uniform partition constants DO stay uniform

If the SAME analytic theorem holds for the three true moving component sources with a bound T, with constant independent of R and H, then the elementary quadratic inequality gives

    sum_R (A_R+B_R+C_R)^2 <= 3*sum_R(A_R^2+B_R^2+C_R^2)
                           <= 9*T.

The new Lean theorem oaiPaired_threeUniformDyadicEnergy formalizes exactly this statement with the moving Euler sources. The number three changes the constant only, NEVER the exponent. The assertion that moving partitions automatically lose uniform constants is false.

Crucial quantifier distinction: the *three specific physical source masks* must lie in the original OpenAI admissible uniform moment family. The original theorem has an explicit W parameter family; it does not quantify over ALL possible moving weights. This is a statement applicability gap, not an obstruction caused by having three partitions.

For the six nonempty site/prime-owner crossed cells, analogous transfer changes the constant by at most 36, if each cell has an independent uniform moment bound with the correct source normalization. Such separate bounds might lose the useful signed cross cancellation, so prefer a uniform estimate on the already compensated *combined source*.

## 3. Inspecting actual pinned OpenAI quantified moment theorems

Original repository: openai/math at commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a, Lean 4.34.1.

- Inverse moment: lean/OAI/NumberTheory/DirichletL/Detector/DetectorInverseRawField.lean, fixed_raw_profiles and source_batch_inverse_raw. The constant C is uniform over U, cutoff tstar, shift r, selected reverse orientation, polynomial log-derivatives n<=2, and admissible height/frequency, **within** W=twistProfile(logTest(orientedProfile(reverse,inverseTest(U,tstar,r))) n, ...), and scaleProfile variants. This is genuinely a moving family of uniform tests, but NOT an arbitrary piecewise indicator or unverified sharp cofactor/window mask.
- Original definition: lean/OAI/NumberTheory/DirichletL/Hecke/InverseAmplificationRaw.lean::RawMoment. This is a bound for the row-energy sum over ideal-character fibers of a polynomial with test profile W, not a dyadic R-average of integer Mobius sharp blocks.
- Marked plain moment: lean/OAI/NumberTheory/DirichletL/Detector/DetectorPlainMarkedFineField.lean::source_batch_plain_marked_fine. The source-specific fourth moment uses selected ideal rows and smooth positive-annular profiles; the theorem takes PositiveFineSourceInput S mesh as an explicit input (discharged elsewhere for the original source in the terminal certificate).
- Local compensation: lean/OAI/NumberTheory/DirichletL/Detector/Local.lean::continued_normalized_cancellation. This is the local marked-minus-rescaled Euler scalar cancellation under explicit B*D=vInv and vInv*W=q. It is a genuine signed cancellation mechanism, but its scalar local factors are not identified with the newly chosen sharp integer cutoffs.

**If one establishes that the true three moving physical masks belong to an admissible uniform OAI test family, including source normalization and mixed Hecke phases, the partition count itself causes no exponent loss.** That bridge remains to be proven; we must not invent its input hypotheses.

## 4. Why certified 7/8 global result alone cannot imply sharp shell L2

Certified global square-block energy is the SQUARE OF A SUM, with cross-shell pairs:

    |sum_(R<K) Delta_R|^2 = |M(K^2-1)|^2
                            <<_eps K^(7/2+eps).

The desired sampled moment is a SUM OF SQUARES, WITHOUT cross-shell pairs:

    E_sharp(H) = sum_(H<=R<2H) Delta_R^2
                     <<_eps H^(5/2-eta+eps), eta>0.

The separate new Lean module OAI_SQUARE_GLOBAL_TO_LOCAL_MOMENT_NO_GO_20261028.lean constructs a deterministic, NON-Mobius signed square-block sequence with F(R)=(-1)^(R+1)R satisfying |F(R)|<=R (stronger than the imported 7/8 bound), while |F(R+1)-F(R)|=2R+1 and its dyadic shell energy is >=4H^3. This is a rigorous counterexample to relying on the terminal global bound alone. It is not a counterexample to the real Mobius goal.

## 5. Sharp localization costs and possible ways around them

The physical square-shell length is 2R+1 at scale X~R^2, so relative width is ~1/R. Original OAI profiles are smooth and their constants depend on test-function family/seminorm constraints.

If one pays sharp-minus-smoothed transition errors ONLY by counting all signed site errors absolutely, a physical transition width w_H produces dyadic energy O(H*w_H^2). To place this trivially controlled error below H^(5/2-eta), one requires w_H << H^(3/4-eta/2) (up to epsilon), giving a normalized transition <= H^(-5/4-eta/2), and hence profile derivatives >= H^(5/4+eta/2). This is NOT a proof that a more clever signed boundary estimate or BV-type uniform theorem is impossible. It is a precise reason the old OAI fixed-profile constant cannot be silently substituted into an R-dependent sharp window.

## 6. Exact independent target on the ACTUAL OAI norm-coefficient carrier

For some eta>0, all epsilon>0, prove with a uniform C_epsilon:

    sum_(H<=R<2H) |sum_(m,d: R^2<=md<(R+1)^2)
                          a_F(m)*chi_{-3}(d)|^2
        <= C_epsilon H^(5/2-eta+epsilon).

Then the proved native equalities and dyadic Cauchy/telescoping yield an improvement below 7/8 for M(X) (exponent 7/8-eta/4+epsilon). This moment does NOT follow from the known OAI 7/8 terminal certificate, and no new exponent improvement is claimed in this PR.

Verdict: The *source equality and partition-uniformity closure* are now formalized. The sole genuinely new analytic input is applicability of uniform OAI compensated moments to the ORIGINAL moving sharp source (or an equivalent signed boundary localization inequality). Preserve all signed cross terms; do not independently bound large prime and cofactor populations by absolute values.