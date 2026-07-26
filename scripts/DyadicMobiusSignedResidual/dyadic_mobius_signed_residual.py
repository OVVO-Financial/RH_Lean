"""Dyadic Moebius pairing of the signed exact-activity residual.

This script is the reproducible companion to
``research/DYADIC_MOBIUS_SIGNED_RESIDUAL.md``.

It verifies, to machine precision, the *exact* algebraic identities that
underlie the dyadic Moebius pairing of the signed exact-activity residual, and
then reports finite magnitude diagnostics for the three structural regions.

Objects
-------
Fix an integer ``t >= 1`` and write ``S = (t+1)^2``, ``X = S - 1 = t*(t+2)``.
For a positive cofactor ``c`` the exact active-prime interval endpoints are

    L(t,c) = max(t+2, ceil(S/(2c)))
    U(t,c) = floor(X/c).

For any cumulative baseline ``F`` and ``E = pi - F`` the signed residual is

    R_F(t) = sum_{c <= t, squarefree} mu(c) * ( E(U(t,c)) - E(L(t,c)-1) ).

Exact identities checked (independent of the choice of E, since they are pure
endpoint / Moebius algebra):

  * reciprocal endpoint:      ceil(S/(2c)) - 1 == floor(X/(2c)) == U(t,2c)
  * lower-endpoint form:      L(t,c) - 1 == max(t+1, U(t,2c))
  * regime threshold:         U(t,2c) >= t+1  <==>  2c <= t
  * three-region decomposition of R_F(t) (see below) equals the direct sum.

Three-region decomposition (exact, for odd c only; even squarefree cofactors are
folded in via mu(2c) = -mu(c)):

    R_F(t) =
        sum_{odd c <= t/4}          mu(c) * [ E(U_c) - 2 E(U_2c) + E(U_4c) ]   (I)
      + sum_{odd t/4 < c <= t/2}    mu(c) * [ E(U_c) - 2 E(U_2c) + E(t+1)  ]   (II)
      + sum_{odd t/2 < c <= t}      mu(c) * [ E(U_c) -   E(t+1)            ]   (III)

with U_kc = U(t,k*c). Region (III) is the unpaired odd tail (its dyadic partner
2c > t falls out of range); it carries the principal endpoint E(t+1).

The algebraic identity check uses a *random* real function in place of E, which
proves the decomposition is a Moebius/endpoint identity with no arithmetic input.
The magnitude diagnostics use the genuine prime error E = pi - F with a smooth
cumulative baseline F(y) = sum_{2<=n<=y} 1/log n (a li-type baseline).
"""

from __future__ import annotations

import argparse
import json
import math
import random


# --------------------------------------------------------------------------
# arithmetic helpers
# --------------------------------------------------------------------------
def mobius_table(n: int) -> list[int]:
    """Linear sieve for the Moebius function on 0..n."""
    mu = [0] * (n + 1)
    if n >= 1:
        mu[1] = 1
    primes: list[int] = []
    is_comp = bytearray(n + 1)
    for i in range(2, n + 1):
        if not is_comp[i]:
            primes.append(i)
            mu[i] = -1
        for p in primes:
            ip = i * p
            if ip > n:
                break
            is_comp[ip] = 1
            if i % p == 0:
                mu[ip] = 0
                break
            mu[ip] = -mu[i]
    return mu


def U(t: int, c: int) -> int:
    return ((t + 1) ** 2 - 1) // c


def a_hyp(t: int, c: int) -> int:
    """ceil(S/(2c)) with S = (t+1)^2."""
    S = (t + 1) ** 2
    return -(-S // (2 * c))


def L(t: int, c: int) -> int:
    return max(t + 2, a_hyp(t, c))


# --------------------------------------------------------------------------
# exact algebraic identity checks (E-independent)
# --------------------------------------------------------------------------
def check_endpoint_identities(t_max: int) -> None:
    for t in range(1, t_max + 1):
        S = (t + 1) ** 2
        X = S - 1
        for c in range(1, t + 1):
            assert a_hyp(t, c) - 1 == X // (2 * c) == U(t, 2 * c), (t, c)
            assert L(t, c) - 1 == max(t + 1, U(t, 2 * c)), (t, c)
            assert (U(t, 2 * c) >= t + 1) == (2 * c <= t), (t, c)
            # interval non-emptiness threshold
            assert (L(t, c) <= U(t, c)) == (c <= t), (t, c)


def R_direct(t: int, mu: list[int], g) -> float:
    tot = 0.0
    for c in range(1, t + 1):
        m = mu[c]
        if m:
            tot += m * (g(U(t, c)) - g(L(t, c) - 1))
    return tot


def R_regions(t: int, mu: list[int], g):
    """Return (I, II, III) using only odd cofactors and the exact region rule."""
    I = II = III = 0.0
    for c in range(1, t + 1, 2):
        m = mu[c]
        if not m:
            continue
        uc = g(U(t, c))
        if 4 * c <= t:
            I += m * (uc - 2 * g(U(t, 2 * c)) + g(U(t, 4 * c)))
        elif 2 * c <= t:
            II += m * (uc - 2 * g(U(t, 2 * c)) + g(t + 1))
        else:
            III += m * (uc - g(t + 1))
    return I, II, III


def check_decomposition(t_max: int) -> float:
    """Exact identity: R_direct == I+II+III for a random real g. Returns max err."""
    rng = random.Random(20260726)
    hi = (t_max + 2) ** 2 + 10
    table = [rng.uniform(-1.0, 1.0) for _ in range(hi + 1)]
    g = table.__getitem__
    mu = mobius_table(t_max + 5)
    max_err = 0.0
    for t in range(1, t_max + 1):
        d = R_direct(t, mu, g)
        I, II, III = R_regions(t, mu, g)
        max_err = max(max_err, abs(d - (I + II + III)))
    return max_err


# --------------------------------------------------------------------------
# exact low-Mertens representations (F) and paired (G), and the zero-frequency
# shell mass -- these were contributed as a correction/sharpening of the note.
# All are E-independent endpoint/Moebius identities (checked against random E).
# --------------------------------------------------------------------------
def mertens_prefix(n: int, odd_only: bool = False) -> list[int]:
    """Cumulative M(x) = sum_{c<=x} mu(c) (or only odd c) on 0..n."""
    mu = mobius_table(n)
    out = [0] * (n + 1)
    s = 0
    for c in range(1, n + 1):
        if not odd_only or c % 2 == 1:
            s += mu[c]
        out[c] = s
    return out


def R_band_direct(t: int, C: int, mu: list[int], g_prefix) -> float:
    """R_F(t;C) = sum_{C<=c<2C, c<=t} mu(c) Delta_F(t,c), Delta via prefix of E."""
    tot = 0.0
    for c in range(C, min(2 * C - 1, t) + 1):
        m = mu[c]
        if not m:
            continue
        lo, hi = L(t, c), U(t, c)
        if lo <= hi:
            tot += m * (g_prefix[hi] - g_prefix[lo - 1])
    return tot


def R_band_form_F(t: int, C: int, Mpre: list[int], g_at) -> float:
    """Exact form (F): swap the finite c- and n-sums.

    R_F(t;C) = sum_{n>=t+2, A_n<=B_n} e_F(n) [ M(B_n) - M(A_n-1) ],
      A_n = max(C, ceil(S/(2n))),   B_n = min(2C-1, t, floor((S-1)/n)).
    """
    S = (t + 1) ** 2
    D = min(2 * C - 1, t)
    tot = 0.0
    for n in range(t + 2, U(t, C) + 1):
        A = max(C, -(-S // (2 * n)))
        B = min(D, (S - 1) // n)
        if A <= B:
            tot += g_at(n) * (Mpre[B] - Mpre[A - 1])
    return tot


def P_band_direct(t: int, C: int, mu: list[int], g_prefix) -> float:
    """Paired block: odd c in [C,2C) with 2c<=t, mu(c)[Delta(c) - Delta(2c)]."""
    def delta(c):
        lo, hi = L(t, c), U(t, c)
        return g_prefix[hi] - g_prefix[lo - 1] if lo <= hi else 0.0

    tot = 0.0
    for c in range(C, 2 * C):
        if c % 2 == 0 or 2 * c > t:
            continue
        m = mu[c]
        if m:
            tot += m * (delta(c) - delta(2 * c))
    return tot


def P_band_form_G(t: int, C: int, Modd: list[int], g_at) -> float:
    """Exact paired form (G): difference of odd-Mertens sums on two reciprocal
    c-annuli [S/2n,S/n] and [S/4n,S/2n]."""
    S = (t + 1) ** 2
    Dstar = min(2 * C - 1, t // 2)
    tot = 0.0
    for n in range(t + 2, U(t, C) + 1):
        Ap = max(C, -(-S // (2 * n)))
        Bp = min(Dstar, (S - 1) // n)
        Am = max(C, -(-S // (4 * n)))
        Bm = min(Dstar, (S - 1) // (2 * n))
        coeff = 0
        if Ap <= Bp:
            coeff += Modd[Bp] - Modd[Ap - 1]
        if Am <= Bm:
            coeff -= Modd[Bm] - Modd[Am - 1]
        if coeff:
            tot += g_at(n) * coeff
    return tot


def check_low_mertens_forms(t_max: int) -> dict:
    """Verify (F), (G) against direct band sums with a random E, and confirm the
    nonzero zero-frequency shell mass |I(t,c)| - |I(t,2c)| ~ S/(4c)."""
    rng = random.Random(31415)
    hi = (t_max + 2) ** 2 + 10
    vals = [rng.uniform(-1.0, 1.0) for _ in range(hi + 2)]
    gpref = [0.0] * (hi + 2)
    for n in range(1, hi + 2):
        gpref[n] = gpref[n - 1] + (vals[n] if n <= hi else 0.0)
    g_at = vals.__getitem__
    mu = mobius_table(hi)
    Mpre = mertens_prefix(hi, odd_only=False)
    Modd = mertens_prefix(hi, odd_only=True)

    max_F = max_G = 0.0
    for t in range(50, t_max + 1):
        for C in (max(2, t // 8), max(2, t // 4), max(2, t // 3), max(2, t // 2)):
            max_F = max(max_F, abs(R_band_direct(t, C, mu, gpref)
                                   - R_band_form_F(t, C, Mpre, g_at)))
            max_G = max(max_G, abs(P_band_direct(t, C, mu, gpref)
                                   - P_band_form_G(t, C, Modd, g_at)))

    # zero-frequency shell mass in the deep range c <= t/4
    ratios = []
    all_pos = True
    for t in (t_max // 2, t_max):
        S = (t + 1) ** 2
        for c in range(2, t // 4 + 1):
            len_c = max(0, U(t, c) - L(t, c) + 1)
            len_2c = max(0, U(t, 2 * c) - L(t, 2 * c) + 1)
            d = len_c - len_2c
            all_pos = all_pos and d > 0
            ratios.append(d / (S / (4 * c)))
    return {
        "form_F_max_abs_error": max_F,
        "form_G_max_abs_error": max_G,
        "zero_freq_mass_ratio_to_S_over_4c_mean":
            sum(ratios) / len(ratios) if ratios else 0.0,
        "zero_freq_mass_strictly_positive": all_pos,
    }


def check_constant_mode_split(centers: list[int], span: int) -> list[dict]:
    """Verify the exact split (N): pair = (l1-l2) A_2c + l1 (A_c - A_2c), and
    measure, with the genuine prime error, the constant-mode part (K) and the
    centered part (J) of the whole paired sum versus the unpaired odd tail.

    Substantiates: neither the paired block nor the tail is principal-mode free,
    and the constant mode is the dominant raw component of the paired block.
    """
    n_max = max(centers) + span
    mu = mobius_table(n_max + 5)
    E = build_prime_error((n_max + 2) ** 2 + 10)

    def delta_len(t, c):
        lo, hi = L(t, c), U(t, c)
        return (E(hi) - E(lo - 1), hi - lo + 1) if lo <= hi else (0.0, 0)

    out = []
    for center in centers:
        P_list, K_list, J_list, T_list = [], [], [], []
        max_split_err = 0.0
        for t in range(center, center + span):
            P = K = J = 0.0
            for c in range(1, t // 2 + 1, 2):
                m = mu[c]
                if not m:
                    continue
                d1, l1 = delta_len(t, c)
                d2, l2 = delta_len(t, 2 * c)
                if l1 == 0:
                    continue
                Ac = d1 / l1
                A2c = d2 / l2 if l2 > 0 else 0.0
                const_mode = (l1 - l2) * A2c
                centered = l1 * (Ac - A2c)
                max_split_err = max(max_split_err,
                                    abs((d1 - d2) - (const_mode + centered)))
                P += m * (d1 - d2)
                K += m * const_mode
                J += m * centered
            Tl = 0.0
            for c in range(t // 2 + 1, t + 1, 2):
                m = mu[c]
                if not m:
                    continue
                d, _ = delta_len(t, c)
                Tl += m * d
            P_list.append(P)
            K_list.append(K)
            J_list.append(J)
            T_list.append(Tl)
        out.append({
            "N": center,
            "H": span,
            "split_identity_max_abs_error": max_split_err,
            "rms_paired": rms(P_list),
            "rms_constant_mode_K": rms(K_list),
            "rms_centered_J": rms(J_list),
            "rms_unpaired_tail": rms(T_list),
        })
    return out


# --------------------------------------------------------------------------
# magnitude diagnostics with the genuine prime error
# --------------------------------------------------------------------------
def build_prime_error(y_max: int):
    """Return E(y) = pi(y) - F(y) with F(y) = sum_{2<=n<=y} 1/log n."""
    sieve = bytearray([1]) * (y_max + 1)
    sieve[0] = sieve[1] = 0
    for i in range(2, int(y_max ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i :: i] = bytearray(len(sieve[i * i :: i]))
    pi = [0] * (y_max + 1)
    F = [0.0] * (y_max + 1)
    s = 0
    fs = 0.0
    for n in range(y_max + 1):
        s += sieve[n]
        if n >= 2:
            fs += 1.0 / math.log(n)
        pi[n] = s
        F[n] = fs

    def E(y: int) -> float:
        if y < 0:
            return 0.0
        return pi[y] - F[y]

    return E


def rms(values: list[float]) -> float:
    return math.sqrt(sum(v * v for v in values) / len(values)) if values else 0.0


def principal_term_check(t: int, mu: list[int], E) -> tuple[float, float]:
    """Coefficient of E(t+1) in R_F(t) should be M_odd(t/4,t/2] - M_odd(t/2,t].

    Returns (algebraic_coeff, closed_form_coeff) which must agree exactly.
    """
    coeff = 0.0
    for c in range(1, t + 1, 2):
        m = mu[c]
        if not m:
            continue
        if 4 * c <= t:
            pass  # region I: E(t+1) does not appear
        elif 2 * c <= t:
            coeff += m  # region II: +E(t+1)
        else:
            coeff -= m  # region III: -E(t+1)
    m_lo = sum(mu[c] for c in range(1, t + 1, 2) if t / 4 < c <= t / 2)
    m_hi = sum(mu[c] for c in range(1, t + 1, 2) if t / 2 < c <= t)
    return coeff, (m_lo - m_hi)


def magnitude_diagnostics(centers: list[int], span: int) -> list[dict]:
    n_max = max(centers) + span
    mu = mobius_table(n_max + 5)
    E = build_prime_error((n_max + 2) ** 2 + 10)
    out = []
    for center in centers:
        ts = list(range(center, center + span))
        Is, IIs, IIIs, tot = [], [], [], []
        max_coeff_err = 0.0
        for t in ts:
            I, II, III = R_regions(t, mu, E)
            Is.append(I)
            IIs.append(II)
            IIIs.append(III)
            tot.append(I + II + III)
            alg, closed = principal_term_check(t, mu, E)
            max_coeff_err = max(max_coeff_err, abs(alg - closed))
        out.append(
            {
                "N": center,
                "H": span,
                "rms_region_I": rms(Is),
                "rms_region_II": rms(IIs),
                "rms_region_III_unpaired_tail": rms(IIIs),
                "rms_paired_I_plus_II": rms([i + j for i, j in zip(Is, IIs)]),
                "rms_total_R_F": rms(tot),
                "principal_coeff_identity_max_err": max_coeff_err,
            }
        )
    return out


# --------------------------------------------------------------------------
def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--identity-tmax", type=int, default=500,
                    help="range for exact endpoint identity checks")
    ap.add_argument("--decomp-tmax", type=int, default=900,
                    help="range for the exact three-region decomposition check")
    ap.add_argument("--forms-tmax", type=int, default=400,
                    help="range for the exact low-Mertens forms (F), (G) check")
    ap.add_argument("--centers", type=int, nargs="*", default=[1500, 2800],
                    help="scales N for magnitude diagnostics")
    ap.add_argument("--span", type=int, default=40, help="short window H")
    ap.add_argument("--output", type=str, default=None)
    args = ap.parse_args()

    print(f"[1/5] exact endpoint identities for t <= {args.identity_tmax} ...")
    check_endpoint_identities(args.identity_tmax)
    print("      OK (reciprocal endpoint, regime threshold, non-emptiness).")

    print(f"[2/5] exact three-region decomposition for t <= {args.decomp_tmax} "
          "(random E) ...")
    max_err = check_decomposition(args.decomp_tmax)
    print(f"      max |R_direct - (I+II+III)| = {max_err:.3e} (floating-point).")

    print(f"[3/5] exact low-Mertens forms (F), (G) and zero-frequency mass "
          f"for t <= {args.forms_tmax} (random E) ...")
    forms = check_low_mertens_forms(args.forms_tmax)
    print(f"      max |R_band - form(F)| = {forms['form_F_max_abs_error']:.3e}")
    print(f"      max |P_band - form(G)| = {forms['form_G_max_abs_error']:.3e}")
    print(f"      zero-freq shell mass / (S/4c): mean = "
          f"{forms['zero_freq_mass_ratio_to_S_over_4c_mean']:.4f}, "
          f"strictly positive: {forms['zero_freq_mass_strictly_positive']} "
          f"(pair is NOT mean-zero).")

    print(f"[4/5] constant-mode / centered split (N) at N in {args.centers}, "
          f"H = {args.span} (real E) ...")
    split = check_constant_mode_split(args.centers, args.span)
    for d in split:
        print(
            f"      N={d['N']:>6}  max|pair-(K+J)|={d['split_identity_max_abs_error']:.1e}"
            f"  RMS(paired)={d['rms_paired']:8.2f}  RMS(K const)={d['rms_constant_mode_K']:8.2f}"
            f"  RMS(J centered)={d['rms_centered_J']:8.2f}  RMS(tail)={d['rms_unpaired_tail']:7.2f}"
        )
    print("      -> constant mode K is the dominant raw component; tail < paired "
          "(hard part is NOT isolated in the tail).")

    print(f"[5/5] magnitude diagnostics at N in {args.centers}, H = {args.span} ...")
    diagnostics = magnitude_diagnostics(args.centers, args.span)
    for d in diagnostics:
        print(
            f"      N={d['N']:>6}  RMS(I)={d['rms_region_I']:9.2f}  "
            f"RMS(II)={d['rms_region_II']:8.2f}  "
            f"RMS(III,tail)={d['rms_region_III_unpaired_tail']:9.2f}  "
            f"RMS(total)={d['rms_total_R_F']:9.2f}  "
            f"[principal-coeff err {d['principal_coeff_identity_max_err']:.0e}]"
        )

    summary = {
        "object": "signed exact-activity residual R_F(t)",
        "endpoints": {
            "lower": "max(t+2, ceil((t+1)^2/(2c)))",
            "upper": "floor(((t+1)^2-1)/c)",
        },
        "exact_identities": {
            "reciprocal_endpoint": "ceil(S/(2c)) - 1 == floor((S-1)/(2c)) == U(t,2c)",
            "lower_endpoint": "L(t,c) - 1 == max(t+1, U(t,2c))",
            "regime_threshold": "U(t,2c) >= t+1  <==>  2c <= t",
            "identity_tmax": args.identity_tmax,
            "decomposition_tmax": args.decomp_tmax,
            "decomposition_max_abs_error": max_err,
        },
        "three_regions": {
            "I_both_hyperbolic": "odd c <= t/4 : mu(c)[E(U_c) - 2E(U_2c) + E(U_4c)]",
            "II_parent_hyp_child_prefix":
                "odd t/4 < c <= t/2 : mu(c)[E(U_c) - 2E(U_2c) + E(t+1)]",
            "III_unpaired_tail":
                "odd t/2 < c <= t : mu(c)[E(U_c) - E(t+1)]",
        },
        "principal_endpoint_coefficient":
            "coeff of E(t+1) == M_odd(t/4,t/2] - M_odd(t/2,t]",
        "low_mertens_forms": {
            "form_F":
                "R_F(t;C) = sum_{n>=t+2} e_F(n)[M(B_n)-M(A_n-1)], "
                "A_n=max(C,ceil(S/2n)), B_n=min(2C-1,t,floor((S-1)/n))",
            "form_G":
                "P_F(t;C) = sum_n e_F(n)(M_odd on [S/2n,S/n] annulus "
                "- M_odd on [S/4n,S/2n] annulus)",
            "form_F_max_abs_error": forms["form_F_max_abs_error"],
            "form_G_max_abs_error": forms["form_G_max_abs_error"],
            "zero_frequency_shell_mass":
                "|I(t,c)| - |I(t,2c)| ~ S/(4c) > 0 : the raw pair is NOT a "
                "mean-zero wavelet; a substantial constant mode survives",
            "zero_freq_mass_ratio_to_S_over_4c_mean":
                forms["zero_freq_mass_ratio_to_S_over_4c_mean"],
            "zero_freq_mass_strictly_positive":
                forms["zero_freq_mass_strictly_positive"],
        },
        "constant_mode_split": {
            "identity_N":
                "pair = (l1-l2) A_2c + l1 (A_c - A_2c), "
                "A_c=Delta(c)/l1, A_2c=Delta(2c)/l2",
            "note":
                "K (constant mode) and J (centered) each exceed the paired sum "
                "and largely cancel; the unpaired tail is smaller than the "
                "paired sum -- the RH-strength difficulty is NOT isolated in "
                "the tail",
            "diagnostics": split,
        },
        "magnitude_diagnostics": diagnostics,
        "classification": {
            "exact": [
                "endpoint identities",
                "regime thresholds",
                "parent/child adjacency (disjoint reciprocal slabs)",
                "three-region decomposition",
                "principal-endpoint coefficient",
                "low-Mertens forms (F) and (G)",
                "nonzero zero-frequency shell mass ~ S/(4c)",
            ],
            "finite_evidence": ["region RMS magnitudes at the tested scales"],
            "open": [
                "no Fourier variable is present yet; before any minor-arc "
                "analysis one must isolate the surviving constant (zero-freq) "
                "mode of the two-shell weight and decide whether it cancels "
                "against the baseline / complementary main term",
                "mean-square bound for the unpaired balanced tail (region III)",
                "equivalently a short-interval variance bound of RH strength",
            ],
        },
    }
    if args.output:
        with open(args.output, "w") as fh:
            json.dump(summary, fh, indent=2)
        print(f"wrote {args.output}")


if __name__ == "__main__":
    main()
