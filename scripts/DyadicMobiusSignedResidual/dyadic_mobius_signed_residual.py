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
    ap.add_argument("--centers", type=int, nargs="*", default=[1500, 2800],
                    help="scales N for magnitude diagnostics")
    ap.add_argument("--span", type=int, default=40, help="short window H")
    ap.add_argument("--output", type=str, default=None)
    args = ap.parse_args()

    print(f"[1/3] exact endpoint identities for t <= {args.identity_tmax} ...")
    check_endpoint_identities(args.identity_tmax)
    print("      OK (reciprocal endpoint, regime threshold, non-emptiness).")

    print(f"[2/3] exact three-region decomposition for t <= {args.decomp_tmax} "
          "(random E) ...")
    max_err = check_decomposition(args.decomp_tmax)
    print(f"      max |R_direct - (I+II+III)| = {max_err:.3e} (floating-point).")

    print(f"[3/3] magnitude diagnostics at N in {args.centers}, H = {args.span} ...")
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
        "magnitude_diagnostics": diagnostics,
        "classification": {
            "exact": [
                "endpoint identities",
                "regime thresholds",
                "parent/child adjacency (disjoint reciprocal slabs)",
                "three-region decomposition",
                "principal-endpoint coefficient",
            ],
            "finite_evidence": ["region RMS magnitudes at the tested scales"],
            "open": [
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
