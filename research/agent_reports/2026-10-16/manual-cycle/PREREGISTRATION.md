# Census pre-registration (written before evaluating R in [1000,5000])
Timestamp: 2026-10-16T08:35:57-04:00
Development range already inspected: R <= 600 only (R = 100, 300, 500, 600 printed).
Evaluation (held-out) range: every R in [1000, 5000]; detailed strata at R = 2500, 4999 (new) and 3162, 4096, 5000 (prior census endpoints, consistency only).

H-CUT band law (Owner-3/4).  Prediction P1: for every R in [1000,5000]
  (a) each eta(q), q in [R,2R), lies in the proved bracket [W/(2q) - int_4^q w/(2q), + w(q)]   (zero violations);
  (b) rho_R = Delta_R - Pred_R lies in [sum lo, sum hi];
  (c) std(rho)/std(Pred) < 0.25 and corr(Delta, Pred) > 0.95 over the range.
Rival N1 (band target-local, no Mertens mode): corr(Delta, Pred) < 0.5 or std(rho) comparable to std(Delta).
Decision: P1 confirmed if (a),(b),(c) hold; any bracket violation REFUTES Owner-2 as implemented.

Descriptive question D1 (not a test of the theorem): fraction of R in [1000,5000] with |Delta_R| > |L_R|.
Descriptive question D2: max |Delta_R|/(R log R) on the range (supertarget regime expected only for very large R).

A/B cut identity (Owner-5): Bdev - cutmode = 0 to floating precision for every R (exact bookkeeping check, not evidence).
Conservation: L_R = F_R - pi(R^2) + 2 for every R (checkL ~ 0); S1+S2+S3+S4 = L.
Correlation test P2: corr(Bdev, -eps(x/3)) > 0.95 over [1000,5000] (prediction from the cut-mode identity: weight 1-w(x/3) ~ 1, other terms O(1/log x)).
