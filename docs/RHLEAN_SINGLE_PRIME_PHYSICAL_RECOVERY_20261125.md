# Physical-multiplicity recovery: single-prime weighted supplier and paid deep tail

**Directive SINGLE_PRIME_PHYSICAL_RECOVERY_V3 (2026-11-25), #1213.** This advances the single-Euler-lever attack, not a new RH endpoint. The V2 fixed-host/Frobenius correspondence remains useful, but the direct multiplicative joint-rank transplant is refuted. Test and prove the quantitative effect of each actual prime insertion instead. All asymptotic proofs below are paper arguments; the attached Lean file submits selected finite and scalar suppliers for hosted verification. No theorem of RH is claimed.

## 1. What survives the rank experiment

For fixed p let P be the product of preceding primes. In a physical square block I_r=[r^2,(r+1)^2-1], let d(r,p) be the number of actual old-wheel survivors after excluding pure powers of p, and b(r,p,k) the number among them divisible by p^k. In the coordinate space with one direction per physical site, the nested spaces E_k have dimensions b_k. If 0<b_j<=b_i<d for i<j, then

    dim(E_i ∩ E_j) = b_j > b_i*b_j/d.

Thus multiplicative independence is structurally false in this model. At p=13, r=53, P=2310, d=22, the only 13-divisible sites are 2873=13^2*17 and 2899=13*223; E_2 has dimension 1. The proposed product rank is 2/22. Neither site is a pure prime power. The finite Lean witness below uses actual finite integer sets.

The previous 15-prime experiment through Rmax=4096 (primes 2..47) found that the half-envelope b_k/d<=2^(-k) held on all 109753 nonzero tested physical layers for p>=5, but the analogous quarter-envelope for p>=13 is NOT universally true. Exact witness p=13,k=9,n=13^9*17=180276489341,r=424589: b_k=1, d=176452; 4^9=262144>d. Distinct occupied old-wheel fibres number 480, so even the half-envelope fails for the distinct-fibre normalization. The new all-prime diagnostic independently retests the nested-site obstruction at R=64,317,1027. At R=1027, 5963 of the raw half-envelope failures are for p=2 and 16 for p=3; none for p>=5. None of this establishes the uniform half-envelope for all physical blocks.

### Fixed-prime deep-layer rate (paper proof)

For fixed p, the old wheel is periodic with positive density V(p-1). As r tends to infinity, d(r,p)=(2r+1)V(p-1)+O_p(1); exclusion of pure p-powers removes at most one site in sufficiently large blocks. Thus d>=c_p H for large r, H=2r+1. Also b_k<=H/p^k+1, and b_k>0 implies H>p^(k/2). Consequently b_k/d<=2/c_p*p^(-k/2) for all sufficiently large k. For the lower limiting rate take r=floor(sqrt(p^k q)) with a fixed prime q>p, giving b_k>=1 and d<=O_p(p^(k/2)). Therefore

    limsup_{k -> infinity} sup_{r>=p,d>0} (b_k/d)^(1/k) = p^(-1/2).

For fixed p>=5, the high-k bound is <=2^(-k) beyond a fixed k0(p). For the remaining finite set of depths the periodic interval count gives b_k/d -> p^(-k)<2^(-k) as r->infinity. Hence the half-envelope holds eventually for each fixed p>=5, uniformly in depth but NOT with a proved p-independent threshold. This fixed-prime argument cannot be used to exchange the p and r quantifiers.

### Upstream recovery mechanism and the actual substitution

At upstream commit 8e5cefeeaffe7e4c12153385b7bb33fb7223c41a, [RestWalk and walk_allBut_bound](https://github.com/leanprover-community/riemann-hypothesis/blob/8e5cefeeaffe7e4c12153385b7bb33fb7223c41a/src/Formalism/SharpRestriction/GrowthBounds/LatticeSystems.lean#L209-L275), [counting_statement_of_block_form](https://github.com/leanprover-community/riemann-hypothesis/blob/8e5cefeeaffe7e4c12153385b7bb33fb7223c41a/src/Formalism/SharpRestriction/GrowthBounds/LatticeSystems.lean#L2396-L2445), and [lengthFromAllBut](https://github.com/leanprover-community/riemann-hypothesis/blob/8e5cefeeaffe7e4c12153385b7bb33fb7223c41a/src/Formalism/SharpRestriction/GrowthBounds/LatticeSystems.lean#L661-L695) obtain a geometric exceptional-rank profile and integrate it into quotient length. We instead establish a direct physical **weighted mass** contraction on an explicit ancestor-closed carrier. This is not a rank theorem, does not discharge admG1, and is not a proof of the upstream signed comparison. It gives an independent native quantitative supplier for depth tails, with a precisely identified normalization correction for the signed source.

## 2. Prime-uniform contraction of the actual weighted cofactor population

Fix R>=2, N=R^2-1, and a prime p<R. V(r)=prod_{q prime<=r}(1-1/q). Extend the actual attenuation to the ancestors using

    a_p(n) = V(max(p,floor(sqrt(n))))/V(p),   n>=1.

It is nonincreasing, belongs to [0,1], and equals the V(r)/V(p) of the original one-step defect on every physical block r>=p. The original weights are

    u_N(n)=N/n-1,       w_N(n)=log(n)*u_N(n),      1<=n<=N.

Define the ancestor-closed carrier Q_p = {m>=p : m has no prime factor <p, and m is not a pure power of p}. Then every m∈Q_p has m>p; multiplication or division by p preserves the non-p prime factors. For d=p^k, k>=1, every physical survivor divisible by d that is not a pure p-power is uniquely d*m with m∈Q_p, m<=N/d. Conversely d*m is an actual surviving physical site n>=p^2. Thus no unearned multiplicity or matching enters the cofactor bijection.

Define

    A_p^+ = sum_{m∈Q_p,m<=N} a_p(m) w_N(m)
    A_p   = sum_{m∈Q_p,p^2<=m<=N} a_p(m) w_N(m)
    L_p   = A_p^+ - A_p = sum_{p<q<p^2,q prime,q<=N} w_N(q)
    C_{p,k} = sum_{m∈Q_p,m<=N/d} a_p(d*m) w_N(d*m).

The low-ancestor sector L_p consists exactly of the primes q between p and p^2: a composite with all factors >=p has size >=p^2. For m<p^2 the attenuation is exactly one. This is the explicit additional normalization, not a free capacity increase. Define A_p^+(0), C_{p,k}(0) by using u_N instead of w_N.

**Pointwise scale identities and inequalities.** Since d>=1, m<=N/d,

    d*u_N(d*m) = u_N(m) - (d-1),
    d*w_N(d*m) = w_N(m) + log(d)*u_N(m) - (d-1)*log(d*m).

As log(m)>=log(p)>0, log(d)=k*log(p) and all original weights are nonnegative,

    u_N(d*m) <= u_N(m)/p^k,
    w_N(d*m) <= ((k+1)/p^k) w_N(m).

Also a_p(d*m)<=a_p(m). Summing over the actual cofactor image proves

    C_{p,k}(0) <= p^(-k)*A_p^+(0),
    C_{p,k} <= (k+1)*p^(-k)*A_p^+ <= (2/p)^k*A_p^+.

This holds uniformly in p,R,k, and the logged half-envelope on this carrier holds for p>=5. For 2 and 3 the exact (k+1)/p^k series is still summable. More strongly, the inequalities hold per old reduced residue s of P: restrict the cofactor sum to m=s mod P and the destination sum to n=p^k*s mod P. The ancestor-closed capacity then supplies the theoretical harmonic cap with the same literal Euler geometric factors as Alpöge:

    sum_{k>=1, odd} C_{p,k}(0) <= [p/(p^2-1)] A_p^+(0),
    sum_{k>=2, even} C_{p,k}(0) <= [1/(p^2-1)] A_p^+(0).

For logged mass the sum of normalized depth bounds over k>=1 is (2*p-1)/(p-1)^2. No assertion of independent rank or probabilistic distribution is required. The logged and harmonic carrier enlargements must be explicitly accounted for; they do not by themselves give an RH-scale estimate.

## 3. Exact signed gain and cost, one prime and one depth at a time

Rearranging the pointwise scaled-log identity on the same physical cofactor frame gives, for d=p^k,

    d*C_{p,k} - A_p
      = L_p + G_{p,k} - T_{p,k} - J_{p,k} - Z_{p,k},

where all five terms on the right are nonnegative:

    G_{p,k} = log(d) * sum_{m∈Q_p,m<=N/d} a_p(d*m) u_N(m)
    T_{p,k} = sum_{m∈Q_p,N/d<m<=N} a_p(m) w_N(m)
    J_{p,k} = sum_{m∈Q_p,m<=N/d} (a_p(m)-a_p(d*m)) w_N(m)
    Z_{p,k} = (d-1) * sum_{m∈Q_p,m<=N/d} a_p(d*m) log(d*m).

Here L_p is the low-prime ancestry credit, G the positive logarithmic prime-power gain, T the top cutoff loss, J the actual later-Euler attenuation loss, and Z the nonhomogeneous normalization cost. This is a native exact signed gain ledger. The sign of the total is not inferred from an unsigned norm.

The attenuation itself traces to successive single-prime insertions. For a=max(p,floor(sqrt(m))), b=max(p,floor(sqrt(d*m))),

    a_p(m)-a_p(d*m) = sum_{a<q<=b,q prime} V(q-1)/(q V(p)).

In particular, swapping the finite sums gives

    J_{p,k} = sum_{p<q<R,q prime} V(q-1)/(q V(p))
               * sum_{m∈Q_p,m<=N/d, m<q^2<=d*m} w_N(m).

Every entry of J is a later-prime Euler debit over a specified cofactor interval. No joint physical rank or new geometric construction is assumed.

**Exact handoff back to #1213.** At k=1, C_{p,1}-A_p/p is the stripped attenuated one-prime defect. To recover the RAW defect, restore

    U_p = (1-1/p) sum_{a>=2,p^a<=N} a_p(p^a) w_N(p^a).

The equality holds because every p^a with a>=2 is removed at its first prime p, and the predicted removal for that site is 1/p of its weight. This U_p is a correction to the old-wheel defect with log(p^a), not the proper-prime-power term with log(p) in the terminal G(N) centering. Keep these distinct and do not pay either twice.

Consequently the original D_N of V1 is exactly

    D_N = sum_{p<R} [ U_p + (L_p+G_{p,1}-T_{p,1}-J_{p,1}-Z_{p,1})/p ].

With the V1 deterministic centering, K_N=D_N-(B_N-M_N). The still-open quantitative supplier is therefore the signed comparison

    sum_{p<R}(T_{p,1}+J_{p,1}+Z_{p,1})/p
       <= sum_{p<R} [U_p+(L_p+G_{p,1})/p]
          -(B_N-M_N) + C_eta R^(1+eta),

for every eta>0 and all sufficiently large R. This is an explicit equivalent attack on the native source; recording the identity is NOT proving this inequality. The credit and expense terms are individually much larger than the desired residual. Earn the comparison by using the actual intervals in the expression for J and the existing owner/Buchstab lemmas, or a proved equivalent supplier. Do not choose a main-term allocation per prime that encodes the desired inequality.

## 4. Unconditional all-prime square-root-scale deep-tail payment

There is a stronger usable conclusion than the fixed-p site-rank experiment. Let H_x=sum_{1<=m<=x}1/m. For each p<R let K_p be the smallest positive k with p^k>=R*p, so p^(K_p-1)>=R. Work on the original physical block I_r, r>=p, and original old-wheel survivor set (either unstripped or consistently stripped). Write A_{r,p,s} for the actual logged weight in old residue s, and B_{r,p,k,t} for the actual weight in residue t divisible by p^k. Let t=p^k*s mod P. Then, after including all fibres and all disjoint physical blocks,

    sum_{r>=p,s} a_p(I_r) |B_{r,p,k,p^k*s}-A_{r,p,s}/p^k|
      <= (2*N*log(N)*H_N)/p^k.

Proof: each attenuation is at most one, each nonnegative weight satisfies w_N(n)<=N*log(N)/n, and the physical terms reindex by n=p^k*m without repeated physical sites at fixed p,k. Thus the actual weighted sum is at most N*log(N)*H_N/p^k. The theoretical capacity sum has the same upper bound because the original physical blocks are disjoint and multiplication by p^k permutes the old reduced residues. The triangle inequality gives the displayed bound even without using signed cancellation.

For every p including 2 and 3,

    sum_{k>=K_p} p^(-k) <= 1/(R*(p-1)).
    
Summing the previous bound over all p<R, and bounding the distinct p-1 denominators by the harmonic sum, proves the unconditional aggregate tail estimate

    sum_{p<R,k>=K_p,r>=p,s} a_p(I_r)
             |B_{r,p,k,p^k*s}-A_{r,p,s}/p^k|
        <= 2*R*log(N)*H_N*H_{R-1}
        = O(R log^3 R)
        = O_eta(R^(1+eta)), for every eta>0.

The infinite geometric reference tail is included, while actual physical layers vanish beyond N. This is an RH-scale budget for the *specified* deep prime-power capacity residual in the weighted physical gain model. It does NOT bound an unrelated rank, determinant, or upstream geometric degree charge, and the original Euler defect D_N uses k=1, not a sum over all k. For any subsequent odd/even gain expansion, this pays the deep tail once, with no assumptions on p or R. Its use in a signed comparison must be made explicit. In particular all k with p^(k-1)>=R can be removed at a proved aggregate cost, leaving only shallow depths. When p^3>N the only non-pure physical layer is k=1. Do not use a finite observation to claim that the remaining shallow layers are uniformly cheap.

## 5. Reproducible tests and audit status

- [Lean finite/scalar suppliers](../research/SINGLE_PRIME_PHYSICAL_RECOVERY_20261125.lean): scaled logarithmic weight law, actual cofactor-image inequality, finite signed ledger, harmonic majorant, geometric cutoff bound, finite nested-support witness. Hosted verification is pending. The full square-block specialization, fixed-p asymptotic and all-prime harmonic aggregation above remain paper proofs.
- [All-prime diagnostic](../scripts/single_prime_weighted_recovery_20261125.js), run with node; [recorded results](single_prime_weighted_recovery_20261125.json). Independent physical enumeration is cross-checked against actual cofactor enumeration. Integer populations, cofactor divisibility, and rank comparisons are exact within the chosen finite range; original logarithmic weights and Euler products are binary64, with scaled cancellation-aware tolerance. This is not a certified real-number enclosure.
- [Prior site-normalization test](../scripts/single_prime_site_recovery_20261125.js), default Rmax=4096, and [exact large witness](../scripts/single_prime_recovery_exact_witness_20261125.py).

| R | incoming primes | physical cofactor checks | signed layer checks | nested joint tests/failures | physical deep + reference upper envelope |
|---:|---:|---:|---:|---:|---:|
|64|18|5881|57|1366/1366|1498.48|
|317|65|152008|173|15815/15815|8290.15|
|1027|172|1617500|414|79805/79805|29887.47|

Total 1,775,389 physical cofactor checks and 644 signed ledger checks passed. No weighted ancestor-half-envelope violations for p>=5. Maximum scaled binary64 identity error 6.22e-14. At R=1027, actual deep mass plus the theoretical reference tail envelope is about 29887.47, below the general all-prime upper bound 3090950.60. The first-depth global ledger gives raw D_N=1264074.42, stripped defect=118893.76 and pure correction=1145180.65, with signed credits L/p=5129107.61 and G/p=6096943.90 versus T/p=4738704.34, J/p=3753294.01 and Z/p=2615159.40. These large terms illustrate why an unsigned or uncentered contraction cannot close RH.

## 6. Seven-role V3 attack instructions

- COORDINATOR: replace the refuted direct independence target by the proved weighted depth cap, the explicit ancestor credit, and the signed first-depth ledger. Track the remaining centered comparison as the only terminal acceptance gate. Preserve #1201 as the final integration PR.
- WHEEL: formalize the exact actual p^k cofactor carrier, residue-by-residue cap, Euler attenuation debit identity, and the pure-power correction. Preserve original block restrictions, non-pure exclusion, and the low-ancestor q sector. Do not turn an assumed bound into a definition.
- CENSUS: extend all-prime tests (not just a fixed finite prime list); stratify L,G,T,J,Z,U by p and q, and locate the first centered loss. Compute the cross-prime interval costs of J, the shallow-depth ledger and the deep bound with actual physical weights. Do not treat normalized mass as rank.
- OWNER: attack the actual shallow signed comparison in section 3 using the displayed q^2/d<=m<q^2 restriction and pre-existing owner/Buchstab identities. Reconcile the gains with cutoff and normalization on the same frame; no freely chosen centering. Trace which portion of Alpöge's local signed ask/gain inequality is replaced, and which still requires a supplying proof.
- ANALYTIC: formalize the all-prime paid deep tail and absorb it once in the original quantifier order. Seek a uniform shallow signed inequality using the explicit later-prime interval and actual low-ancestor primes, not an unproved equidistribution hypothesis.
- REFEREE: challenge the enlarged ancestor carrier, any misuse of harmonic versus logged capacities, the distinct pure-power payments, weighted-versus-rank conflation, signs in the centered comparison, and any promotion of numerical half-envelope or fixed-p thresholds to prime-uniform theorems.
- LEAN: verify the submitted scalar and finite physical suppliers under existing hosted warning-fatal preflight. Formalize the global specialization and actual paid tail, then the signed payment if earned. No new conditional RH endpoint; audit proof dependencies before #1201 integration.

The repository directive is scoped to #1213 and does not itself change or launch external agents. The exact criterion for completion remains the V1 centered lower bound on K_N for every sufficiently large square clock, with its original quantifier order and existing consumer. Hosted CI and human review remain required.

## 7. V4 signed Perron compensation

See [the V4 exact physical alignment, signed attenuation and paid initial-owner sector](RHLEAN_SINGLE_PRIME_PERRON_COMPENSATION_20261125.md). This is a separate quantitative paper supplier from the V3 deep-power tail. V4 supersedes any attempt to pay all prime flips through independent pairings. The high-owner centered comparison remains open, and the new finite Lean suppliers await hosted verification.
