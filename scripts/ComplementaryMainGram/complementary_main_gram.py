"""Complementary main term and joint-Gram diagnostics.

Reproducible companion to ``research/COMPLEMENTARY_MAIN_JOINT_GRAM.md``.

Corrected architecture (handoff): the square-prefix process splits as

    S  =  Main_F  +  (H - Hhat_F)         with   Main_F = L + Hhat_F ,

i.e. the complementary main term plus the signed prime-discrepancy residual, and
the residual is further pairing-decomposed as  R_F = K + J + T  (constant-mode +
centered + unpaired tail, from research/DYADIC_MOBIUS_SIGNED_RESIDUAL.md), so

    S  =  L + Hhat_F - K - J - T .

This script builds every component from one consistent definition set (see
below) over a short window t in [N, N+H), and reports:

  * energies and the internal cancellation of the complementary main L + Hhat_F;
  * the near-projection coefficient alpha_orth(L on -Hhat_F) versus the
    theorem-predicted coefficient 1, and the energy excess of coefficient 1;
  * the contrasting (non-projection) behaviour of Main - R_F;
  * the residual-side Gram, in particular the dominant negative cross term
    2<K,J>, and the negligible K/T, J/T interactions.

Definitions (this harness; consistent with the dyadic exact-activity geometry)
------------------------------------------------------------------------------
For height t and cofactor c, with S=(t+1)^2, exact endpoints
    L(t,c) = max(t+2, ceil(S/(2c))) ,  U(t,c) = floor((S-1)/c) ,
and E(y) = pi(y) - F(y) for a baseline F:

    H[t]      =  sum_{c<=t, odd} -mu(c) ( pi(U) - pi(L-1) )        (signed high)
    Hhat_F[t] =  sum_{c<=t, odd} -mu(c) ( F(U)  - F(L-1)  )        (baseline transport)
    S[t]      =  M_odd((t+1)^2 - 1) - M_odd(ceil((t+1)^2/2) - 1)   (odd dyadic annulus)
    L[t]      =  S[t] - H[t]                                        (born-smooth)
    Main[t]   =  L[t] + Hhat_F[t]
    RF_odd[t] =  Main[t] - S[t] = Hhat_F[t] - H[t]                  (physical residual)

The odd-cofactor closure  S = Main - RF_odd  holds EXACTLY (checked; max err 0).

K, J, T are the constant-mode / centered / tail pieces of the dyadic PAIRING
residual (research/DYADIC_MOBIUS_SIGNED_RESIDUAL.md). The pairing folds even
cofactors 2c back onto odd c via mu(2c) = -mu(c), so RF_pair = K + J + T is the
ALL-cofactor reorganization and differs from the odd-only physical residual
RF_odd by the even-cofactor terms. The script reports this convention gap rather
than forcing a false unified closure.

IMPORTANT CAVEAT. The exact born-smooth/high split and the baseline choice fix
the finer coefficients (survival %, alpha_orth, projection ratios) but not the
*qualitative* conclusions. A collaborator report using a Li baseline at
(N,H)=(2800,640) found e.g. survival 0.0037%, cosine -0.99997, alpha_orth 0.997;
this harness (trapezoidal 1/log baseline, born-smooth = annulus - high) reproduces
the same phenomena but with amplitudes differing by ~2x, i.e. the exact digits are
definition/baseline/scale sensitive. Treat the *structure*, not the digits, as the
robust output. The `--baseline` switch and the (N, H) grid are provided precisely
so this sensitivity can be mapped.
"""

from __future__ import annotations

import argparse
import json
import math


def sieve_pi(n: int) -> list[int]:
    s = bytearray([1]) * (n + 1)
    s[0] = s[1] = 0
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i :: i] = bytearray(len(s[i * i :: i]))
    pi = [0] * (n + 1)
    acc = 0
    for x in range(n + 1):
        acc += s[x]
        pi[x] = acc
    return pi, s


def cum_li(n: int) -> list[float]:
    """Trapezoidal cumulative integral of 1/log from 2 (a li-type baseline)."""
    F = [0.0] * (n + 1)
    acc = 0.0
    prev = None
    for x in range(2, n + 1):
        cur = 1.0 / math.log(x)
        acc += cur if prev is None else 0.5 * (prev + cur)
        F[x] = acc
        prev = cur
    return F


def mobius(n: int) -> list[int]:
    mu = [0] * (n + 1)
    if n >= 1:
        mu[1] = 1
    primes: list[int] = []
    comp = bytearray(n + 1)
    for i in range(2, n + 1):
        if not comp[i]:
            primes.append(i)
            mu[i] = -1
        for p in primes:
            if i * p > n:
                break
            comp[i * p] = 1
            if i % p == 0:
                mu[i * p] = 0
                break
            mu[i * p] = -mu[i]
    return mu


def odd_mertens(mu: list[int]) -> list[int]:
    M = [0] * len(mu)
    acc = 0
    for m in range(1, len(mu)):
        if m & 1:
            acc += mu[m]
        M[m] = acc
    return M


def dot(x, y):
    return sum(a * b for a, b in zip(x, y))


def energy(x):
    return dot(x, x)


def analyse_window(N: int, H: int, pi, F, mu_small, Modd) -> dict:
    def U(t, c):
        return ((t + 1) ** 2 - 1) // c

    def Lo(t, c):
        return max(t + 2, -(-((t + 1) ** 2) // (2 * c)))

    L_, Hh_, Hn_, S_, K_, J_, T_ = [], [], [], [], [], [], []
    for t in range(N, N + H):
        Ssq = (t + 1) ** 2
        Hprime = 0.0
        Hf = 0.0
        K = J = T = 0.0
        for c in range(1, t + 1, 2):
            mc = mu_small[c]
            if mc == 0:
                continue
            lo, hi = Lo(t, c), U(t, c)
            if lo > hi:
                continue
            dpi = pi[hi] - pi[lo - 1]
            dF = F[hi] - F[lo - 1]
            Hprime += (-mc) * dpi
            Hf += (-mc) * dF
            # residual increment E = pi - F
            d1 = dpi - dF
            l1 = hi - lo + 1
            if 2 * c <= t:
                lo2, hi2 = Lo(t, 2 * c), U(t, 2 * c)
                l2 = hi2 - lo2 + 1
                d2 = (pi[hi2] - pi[lo2 - 1]) - (F[hi2] - F[lo2 - 1]) if lo2 <= hi2 else 0.0
                Ac = d1 / l1
                A2c = d2 / l2 if l2 > 0 else 0.0
                K += mc * ((l1 - l2) * A2c)
                J += mc * (l1 * (Ac - A2c))
            else:
                T += mc * d1
        Sann = Modd[Ssq - 1] - Modd[(Ssq + 1) // 2 - 1]
        L_.append(Sann - Hprime)
        Hh_.append(Hf)
        Hn_.append(Hprime)
        S_.append(float(Sann))
        K_.append(K)
        J_.append(J)
        T_.append(T)

    Main = [a + b for a, b in zip(L_, Hh_)]
    # Physical residual is ODD-cofactor: RF_odd = Hhat - H. Then Main - RF_odd = S
    # holds EXACTLY by construction (L := S - H).
    RF_odd = [hf - hn for hf, hn in zip(Hh_, Hn_)]
    max_S_close = max(abs(m - rf - s) for m, rf, s in zip(Main, RF_odd, S_))
    # Pairing residual RF_pair = K + J + T is the ALL-cofactor reorganization
    # (it folds even 2c back in via mu(2c)=-mu(c)); it differs from RF_odd by the
    # even-cofactor terms. Report the gap honestly rather than forcing a closure.
    RF_pair = [a + b + c for a, b, c in zip(K_, J_, T_)]
    conv_gap = energy([p - o for p, o in zip(RF_pair, RF_odd)]) / energy(RF_odd)

    def cos(x, y):
        return dot(x, y) / math.sqrt(energy(x) * energy(y))

    def centered(x):
        mu_ = sum(x) / len(x)
        return [a - mu_ for a in x]

    negHh = [-a for a in Hh_]
    a_orth = dot(L_, negHh) / energy(Hh_)  # L on -Hhat
    resid_opt = [a - a_orth * b for a, b in zip(L_, negHh)]
    aMR = dot(Main, RF_odd) / energy(RF_odd)
    resid_MR_opt = [a - aMR * b for a, b in zip(Main, RF_odd)]

    return {
        "N": N, "H": H,
        "closure_Main_minus_RFodd_eq_S_maxerr": max_S_close,
        "energies": {
            "L": energy(L_), "Hhat": energy(Hh_), "H": energy(Hn_),
            "S": energy(S_), "Main": energy(Main),
            "RF_odd": energy(RF_odd), "RF_pair": energy(RF_pair),
            "K": energy(K_), "J": energy(J_), "T": energy(T_),
        },
        "convention_gap_RFpair_vs_RFodd": conv_gap,
        "complementary_main": {
            "survival_pct": energy(Main) / (energy(L_) + energy(Hh_)) * 100.0,
            "raw_cosine_L_Hhat": cos(L_, Hh_),
            "centered_corr_L_Hhat": cos(centered(L_), centered(Hh_)),
            "alpha_orth_L_on_negHhat": a_orth,
            "gap_from_1": 1.0 - a_orth,
            "energy_excess_coeff1_over_opt": energy(Main) / energy(resid_opt),
        },
        "main_minus_RFodd": {
            "alpha_orth_Main_on_RFodd": aMR,
            "energy_excess_coeff1_over_opt":
                energy([a - b for a, b in zip(Main, RF_odd)]) / energy(resid_MR_opt),
        },
        "residual_pairing_gram_all_cofactor": {
            "2_K_J": 2 * dot(K_, J_),
            "2_K_T": 2 * dot(K_, T_),
            "2_J_T": 2 * dot(J_, T_),
            "2_K_J_over_RFpair_energy": 2 * dot(K_, J_) / energy(RF_pair),
            "centered_corr_K_J": cos(centered(K_), centered(J_)),
        },
    }


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--N", type=int, nargs="*", default=[900, 1200],
                    help="scales N (grid)")
    ap.add_argument("--hratio", type=float, default=0.2,
                    help="H = round(hratio * N)")
    ap.add_argument("--output", type=str, default=None)
    args = ap.parse_args()

    results = []
    for N in args.N:
        H = max(16, round(args.hratio * N))
        maxU = (N + H + 1) ** 2 - 1
        print(f"N={N} H={H}: building arrays to {maxU} ...")
        pi, _ = sieve_pi(maxU)
        F = cum_li(maxU)
        mu_full = mobius(maxU)
        Modd = odd_mertens(mu_full)
        res = analyse_window(N, H, pi, F, mu_full, Modd)
        cm = res["complementary_main"]
        rg = res["residual_pairing_gram_all_cofactor"]
        print(f"   odd-cofactor closure (Main - RF_odd == S) max err = "
              f"{res['closure_Main_minus_RFodd_eq_S_maxerr']:.2e}")
        print(f"   main survival = {cm['survival_pct']:.5f}%  "
              f"cos(L,Hhat) = {cm['raw_cosine_L_Hhat']:.7f}  "
              f"alpha_orth = {cm['alpha_orth_L_on_negHhat']:.6f}  "
              f"coeff1/opt = {cm['energy_excess_coeff1_over_opt']:.3f}")
        print(f"   Main-RF_odd: alpha = {res['main_minus_RFodd']['alpha_orth_Main_on_RFodd']:.4f}  "
              f"coeff1/opt = {res['main_minus_RFodd']['energy_excess_coeff1_over_opt']:.3f}")
        print(f"   [all-cofactor pairing] 2<K,J>/|RF_pair|^2 = {rg['2_K_J_over_RFpair_energy']:.3f}  "
              f"corr(K,J) = {rg['centered_corr_K_J']:.4f}  "
              f"(2<K,T>={rg['2_K_T']:.2e}, 2<J,T>={rg['2_J_T']:.2e})")
        print(f"   convention gap |RF_pair - RF_odd|^2 / |RF_odd|^2 = "
              f"{res['convention_gap_RFpair_vs_RFodd']:.3f}")
        results.append(res)

    summary = {
        "object": "complementary main L+Hhat_F, and residual pairing Gram",
        "definitions": {
            "H": "sum_{c<=t,ODD} -mu(c)(pi(U)-pi(L-1))",
            "Hhat_F": "sum_{c<=t,ODD} -mu(c)(F(U)-F(L-1))",
            "S": "M_odd((t+1)^2-1) - M_odd(ceil((t+1)^2/2)-1)",
            "L": "S - H (born-smooth)",
            "RF_odd": "Hhat_F - H = Main - S (physical, odd cofactor; closes EXACTLY)",
            "RF_pair": "K + J + T (dyadic pairing; ALL-cofactor reorganization)",
        },
        "baseline": "trapezoidal cumulative 1/log (li-type)",
        "reproduced_qualitatively": [
            "near-total cancellation of L+Hhat_F (survival < 0.01%)",
            "raw cosine(L,Hhat) < -0.9999",
            "L+Hhat_F nearly projection-like (alpha_orth close to 1)",
            "Main-RF_odd not projection-like (alpha far from 1)",
            "2<K,J> dominant negative residual cross term; K/T, J/T negligible",
        ],
        "open_reconciliation": [
            "exact digits are definition/baseline/scale sensitive; a Li-baseline "
            "collaborator report at (N,H)=(2800,640) gives ~2x different amplitudes",
            "the physical residual RF_odd is odd-cofactor, but the pairing K+J+T "
            "is the all-cofactor reorganization; they differ by even-cofactor "
            "terms (convention_gap). A unified 5-component [L,Hhat,-K,-J,-T] "
            "closure needs the residual/pairing cofactor convention pinned down.",
        ],
        "grid": results,
    }
    if args.output:
        with open(args.output, "w") as fh:
            json.dump(summary, fh, indent=2)
        print(f"wrote {args.output}")


if __name__ == "__main__":
    main()
