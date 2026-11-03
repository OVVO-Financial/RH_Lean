# RH | Prime Census Laboratory - 2026-11-03

## Early Research Checkpoint

Execution: PARTIAL / IN_PROGRESS. Scheduled invocation at 03:11:01 EST (-0500); RUN_ID_UNAVAILABLE. Checkpoint prepared 2026-11-03 08:17:39 UTC. No new computation is claimed yet.

### Selected Question And Preregistration

Resume the exact small fragment-versus-scalar discriminator in 20261102-coordinator-3, section H, rather than repeat the completed FINITE-AC bootstrap or affine censuses. Main is 8e5d64ae689b39dabd2a4f6eb33efe4d5d192015; reporting intake is a9f0b4abdf051612929d39b463a433ef844c45eb. Policy blobs: AGENTS 9fa5e9519e2fb6dde22217aa2a18982dafef373a; proof contract 88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a; research engine 6fce99c61efb5b2a73c0cb1f1464f09b351fcd55. deployment_ack: NEXT-CENSUS resumed with newer committed evidence and a nonduplicate test.

For each root R, retain the original field
g_R(n)=mu(n)+sum_(q odd prime, q^2<R, q^2|n) mu(n/q^2)/q,
on R^2<=n<(R+1)^2. Freeze g_H^fr by replacing q^2<R with q^2<H.
W_R is the complete shell sum. Omega_R^mov is the largest absolute sum on any contiguous fragment of the same shell, equivalently maximum minus minimum of all its prefix sums, including the empty prefix. Z_R is the actual occurrence-square diagonal. N_R^fr is the unordered distinct-address pair sum of the frozen field.

Fix exploratory H=64,128 and held-out H=256,512 BEFORE scanning. Exact finite candidate tests, proposed here by Census and not attributed to an analyst:
1. SCALAR-4: sum_R (Omega_R^mov)^2 <= 4 sum_R W_R^2.
2. DIAGONAL-2: sum_R [(Omega_R^mov)^2-W_R^2] <= 2 sum_R Z_R.
One exact failure refutes the stated constant on that tested block; no revised constant will be promoted from these data. The rival explanation is that total signed cancellation hides substantial internal excursions, so a scalar energy may not supply the maximal-fragment estimate. Survival is finite evidence only.

For every root write P_R(j)=sum_(R^2<=n<j)g_R(n), and record both endpoint overshoots:
a_R=min(0,W_R)-min_j P_R(j), b_R=max_j P_R(j)-max(0,W_R).
Then Omega_R=|W_R|+a_R+b_R. Reconstruct the complete square and its excess before any norm comparison. Also record every zero W_R, exact extremal roots, frozen/moving differences, root and activation interactions.

Reconstruct the original zero-frequency physical remainder
A_R=M(R-1)-M(R^2-1)-sum_(q odd prime, q^2<R) M(floor((R^2-1)/q^2))/q
and its increment A_(R+1)-A_R=mu(R)-W_R-K_R,
where K_R=M(R+2)/q for R=q^2 with odd prime q and zero otherwise.
Check the complete energy, all four covariance sectors, and C25c:
|sum_R (A_(R+1)-A_R)^2-2 sum_R N_R^fr|<=65H^2.
K_R here is the activation term, NOT the historical FINITE-AC envelope.

Mandatory regressions: s=12,p=3 fragment cancellation; strict q^2=R and q^2=H boundaries; the genuine (3,5) consecutive cell. Two independent Mobius/carrier reconstructions will be used. No scan beyond H=512 is planned absent a new mathematical reason.

### Authority, Continuity And Scope

Read live main instructions, contract, selector, breadth/complete-return/engine/role protocols; actual transport, ledger-splice, address and canonical definitions. Material source blobs: 72d66f61b3eeb000117ecdac393572558bb7c378, 73447e8c73ea60affec36a25b9f4794862331359, 61f98a8997d86ddbb07404284d12aebd36a67955, 8c125b69cc0fbee577d063bcfa606843152868f3.

All relevant November 2 role sections and today's Owner, Analytic and Wheel findings were retrieved. Today Coordinator, Referee, Lean and preceding Census are absent at intake: TODAY=PENDING; YESTERDAY=CARRY_FORWARD. External inbox 038018145c0fddb2f6306c0712373adf9cd1ea52 has no newer than October 18 entry; its old routing is superseded.

Referee 20261102-referee-3 and Coordinator 20261102-coordinator-3 accept the strict gain only on unmerged PR1073@9cbfce5295343bcb411e6d2cb159b59995cd985b. This run will refresh PR/CI state but does not claim an independent re-review of that proof. Main retains the non-strict baseline. Canonical actual-prime VF, sharp shell-energy gain, and RH remain OPEN. This experiment assumes none of those bounds.

Only this dated own report will be published. No Lean execution, source edit, issue/PR mutation, agent launch, or merge. Final exact results, reproducible code, limitations and continuation will be appended.
