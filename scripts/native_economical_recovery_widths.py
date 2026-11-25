"""Exact native WinPair/PageN and positive-width-site diagnostic for RH_Lean #1201.

Run with Python 3. No external packages, floating-point arithmetic, or prime tables
are used. The integral matrices below are the coefficients of the active
width-site reads. Constructing the physical theta section and dual restriction
maps is a separate missing step.
"""

import json
from fractions import Fraction as Q
from itertools import combinations
from math import comb, gcd, isqrt


R = 10**7
N = R**2 - 1
E = 99
DYADIC = 2 ** (E + 2)
Q_PRIME = 3
D = 3814 * 5**400 + 1
TOPS = (1, 17, 47, 43**2)
B = 16
C = 2


def exp_bounds(x, terms=160):
    """Exact rational interval via the positive Taylor series and geometric tail."""
    x = Q(x)
    assert 0 <= x < terms + 1
    summand, partial = Q(1), Q(0)
    for k in range(terms):
        partial += summand
        summand *= x / (k + 1)
    return partial, partial + summand / (1 - x / (terms + 1))


def certify_host():
    # The order of 2 at each prime divisor of D is divisible by 5^400.
    # Each such prime is 1 mod 5^400; since its square is already > D,
    # D has just one prime factor, counted with multiplicity.
    F = 5**400
    assert (D - 1) % F == 0 and (D - 1) % (5 * F) != 0
    assert F * F > D
    assert pow(2, D - 1, D) == 1 and gcd(pow(2, (D - 1) // 5, D) - 1, D) == 1
    assert Q_PRIME == 3 and Q_PRIME % 8 == 3 and D % 16 == 7 and (D + 1) % Q_PRIME == 0
    # 32 < log Y < 33, 11/10 < Y^(eps/5) < 9/8 for Y=N, eps=1/64.
    assert exp_bounds(32)[1] < N < exp_bounds(33)[0]
    assert Q(11, 10) < exp_bounds(Q(32, 320))[0]
    assert exp_bounds(Q(33, 320))[1] < Q(9, 8)
    assert exp_bounds(1)[1] < 3 < exp_bounds(Q(11, 10))[0]
    assert Q(9, 8) / 2 < 1
    # d_small is empty below 9/8. 640 < log d < 820 by d = 3814*5^400+1.
    assert exp_bounds(Q(8, 5))[1] < 5 < exp_bounds(2)[0]
    assert 3815 < exp_bounds(20)[0]
    assert Q(9, 8) * 33**2 / 2 < 640 < 820 < Q(11, 10) * 32**2
    # PageN: 2+8eps=17/8.
    assert N**17 <= 2 ** (8 * E) <= 2**8 * N**17
    # All widths are initially 16; an individual unit increment stays inside h=1.
    # exp(x^eps)<16 and exp(x^(eps/3))/3 < x.
    assert exp_bounds(Q(33, 64))[1] < 2 and exp_bounds(2)[1] < B
    assert exp_bounds(2)[1] / 3 < N
    # In the square constraint a_t/b=N, beta=b=16, Amax=16N, T2=H.
    assert 2 * max(TOPS) * N < DYADIC
    assert N < D


def check_stronger_size_band():
    eps = Q(9, 560)
    assert 0 < eps < Q(1, 52)
    assert Q(11, 10) < exp_bounds(32 * eps / 5)[0]
    assert exp_bounds(33 * eps / 5)[1] < Q(9, 8)
    assert exp_bounds(33 * eps)[1] < 2 and exp_bounds(2)[1] < B
    assert 2 + 8 * eps == Q(149, 70)
    assert N**149 <= 2**(70 * E) <= 2**70 * N**149
    assert (2 + 8 * eps - eps / 100, 2 + 8 * eps + eps / 100) == (
        Q(119191, 56000), Q(119209, 56000))
    assert N**119191 <= 2**(56000 * E) <= N**119209
    assert 2**(6400 * E) > N**13601
    assert exp_bounds(33 * eps / 8)[1] < 2
    assert len(TOPS) * 4 < DYADIC // 4
    assert exp_bounds(33 * 3 * eps / 8)[1] < 2 < 26
    assert Q(11, 5)**4 < 26


def power_of_prime(n):
    """Return (prime, exponent), or None. Called on derived candidates only."""
    if n < 2:
        return None
    p = next((j for j in range(2, isqrt(n) + 1) if n % j == 0), n)
    i = 0
    while n % p == 0:
        n //= p
        i += 1
    return (p, i) if n == 1 else None


def sign_bit(n, ell):
    symbol = pow(n % ell, (ell - 1) // 2, ell)
    assert symbol in (1, ell - 1)
    return int(symbol == ell - 1)


def frobenius(p):
    # In the p-component the original unit is 1, in the coprime
    # complement it is p. The group coordinates are d-sign/q-sign/±unit.
    h = 1 if p == 2 else p % DYADIC
    return (0 if p == D else sign_bit(p, D),
            0 if p == Q_PRIME else sign_bit(p, Q_PRIME), min(h, -h % DYADIC))


def classify(t, p, i):
    """Classify actual non-Phi rows and every original first-return condition."""
    n = p**i
    if n > N:
        return "outside prefix"
    if p in (2, Q_PRIME):
        assert frobenius(p)[0] == 0
        return "ramified, non-Phi read zero"
    assert p != D
    d_bit, q_bit, _ = frobenius(p)
    if d_bit == 0 or i % 2 == 0:
        return "non-Phi read zero"
    # For every displayed and every possible prefix return, no ±wrap:
    # the dyadic coordinate is the ordinary integer t*n.
    assert 2 * t * n < DYADIC
    if q_bit and t * n in TOPS and t * n != t:
        # Equal earlier displacements would imply p^j=p^i in this short range.
        return "first-excluded"
    return "retained"


def active_reads_at_site(bit, h):
    """Invert the positive partner map on ALL t and every 1 <= p^i <= N.

    The inequality 2*max(TOPS)*N < DYADIC reduces equality modulo ± to integer
    equality; t must divide h. This exhausts the prefix without enumerating N.
    """
    reads = []
    for t in TOPS:
        if h % t:
            continue
        pp = power_of_prime(h // t)
        if not pp:
            continue
        p, i = pp
        label = classify(t, p, i)
        if label not in ("retained", "first-excluded"):
            continue
        if 1 - frobenius(p)[1] == bit:
            reads.append((t, p, i, label))
    return reads


def selected_width_rows(p):
    """Smith exponents of the actual width coefficient rows at t=[1]."""
    rows = []
    i = 1
    while p**i <= N:
        n = p**i
        if classify(1, p, i) == "retained":
            bit = 1 - frobenius(p)[1]
            reads = active_reads_at_site(bit, n)
            selected = (1, p, i, "retained")
            assert selected in reads
            others = [r for r in reads if r != selected]
            # At all implicated n and w in [16,17] the original sharp positive
            # part is strictly active, so the coefficient of the width is -1.
            for _, base, exp, _ in reads:
                assert B * N > (B + 1) * base**exp
            rows.append({"i": i, "n": n, "site": [0, bit, n],
                         "other_reads_at_site": others, "depth": C if others else 0})
        i += 1
    assert len({tuple(r["site"]) for r in rows}) == len(rows)
    # At distinct sites each omitted coordinate has its own standard basis lift.
    # A duplicated site gives exactly one restriction v_site in pi^C O; its
    # scaled standard basis lift attains that entire ideal.
    depths = [r["depth"] for r in rows]
    return {"rows": rows, "rank": len(rows), "smith_exponents": depths,
            "Z_local_smith_values": [p**depth for depth in depths],
            "quotient_length": sum(depths),
            "layer_counts": [sum(depth > j for depth in depths) for j in range(C + 1)]}



def matrix_product(left, right):
    return [[sum(a * b for a, b in zip(row, col)) for col in zip(*right)] for row in left]


def bezout(a, b):
    if not b:
        return abs(a), 1 if a >= 0 else -1, 0
    g, x, y = bezout(b, a % b)
    return g, y, x - (a // b) * y


def admissible_basis(rows, size, modulus):
    """Columns span the exact integer preimage of zero modulo the modulus."""
    basis = [[int(i == j) for j in range(size)] for i in range(size)]
    for row in rows:
        values = matrix_product([row], basis)[0]
        for j in range(1, size):
            a, b = values[0], values[j]
            if not b:
                continue
            g, x, y = bezout(a, b)
            for v in basis:
                u, w = v[0], v[j]
                v[0], v[j] = x * u + y * w, (-b // g) * u + (a // g) * w
            values[0], values[j] = g, 0
        multiplier = modulus // gcd(values[0], modulus)
        for v in basis:
            v[0] *= multiplier
    assert all(t % modulus == 0 for row in matrix_product(rows, basis) for t in row)
    return basis


def minor_det(a):
    """Fraction-free elimination with exact integer divisions."""
    if not a:
        return 1
    a = [row[:] for row in a]
    sign, previous = 1, 1
    for i in range(len(a) - 1):
        pivot = next((k for k in range(i, len(a)) if a[k][i]), None)
        if pivot is None:
            return 0
        if i != pivot:
            a[i], a[pivot] = a[pivot], a[i]
            sign = -sign
        for k in range(i + 1, len(a)):
            for j in range(i + 1, len(a)):
                value = a[k][j] * a[i][i] - a[k][i] * a[i][j]
                assert value % previous == 0
                a[k][j] = value // previous
        previous = a[i][i]
    return sign * a[-1][-1]


def smith_factors(matrix):
    """D_j is the gcd of ALL j-minors; Smith factor j is D_j/D_(j-1)."""
    factors, previous = [], 1
    for j in range(1, len(matrix) + 1):
        divisor = 0
        for rows in combinations(range(len(matrix)), j):
            for cols in combinations(range(len(matrix[0])), j):
                m = [[matrix[r][c] for c in cols] for r in rows]
                divisor = gcd(divisor, minor_det(m))
        assert divisor > 0 and divisor % previous == 0
        factors.append(divisor // previous)
        previous = divisor
    return factors


def recompute_width_image(p, selected):
    """Apply E,C to the same widths before and after changing their coordinates.

    Only one positive bit and one fixed (u,j) are varied. Include every p-power
    ancestor of the selected sites in this bit. All other sites give separate
    width coordinates, have zero selected read, and are fixed at zero here.
    Thus extension by zero gives the entire selected image in the full lattice.
    """
    bit = 1 - frobenius(p)[1]
    exponents = list(range(1 + max(r["i"] for r in selected["rows"])))
    sites = [p**i for i in exponents]
    retained = {(1, p, r["i"], "retained") for r in selected["rows"]}
    selected_rows, competing_rows = [], []
    for k, site in enumerate(sites):
        row = [int(j == k) for j in exponents]
        for label in active_reads_at_site(bit, site):
            if label in retained:
                selected_rows.append(row)
            else:
                competing_rows.append(row)
    result = {}
    for z in [0, 16, 32, 64]:
        decoder = [[int(i == j) if z == 0 or p <= z else
                    ((-1)**(j-i) * comb(j, i) if i <= j else 0)
                    for j in exponents] for i in exponents]
        assert minor_det(decoder) == 1
        E, Crows = matrix_product(selected_rows, decoder), matrix_product(competing_rows, decoder)
        lattice = admissible_basis(Crows, len(sites), p**C)
        factors = smith_factors(matrix_product(E, lattice))
        assert factors == selected["Z_local_smith_values"]
        result["original" if z == 0 else str(z)] = factors
    return result


def shifted_height_image(p, selected):
    """Exact integral image on the listed reads with both top heights free.

    On an active site the height coefficient is 1/p**i and the width
    coefficient is -1. Keeping all widths and measured atoms integral makes
    the height increment at each top a multiple of its largest listed p**i.
    Other sites and the geometric restrictions are outside this projection.
    """
    reads = selected["rows"]
    groups = [[(1, p, row["i"], "retained"), *row["other_reads_at_site"]]
              for row in reads]
    height_exponents = {}
    for group in groups:
        for top, base, exponent, label in group:
            assert base == p and label == "retained"
            height_exponents[top] = max(height_exponents.get(top, 0), exponent)
    tops = sorted(height_exponents)

    def active_row(top, exponent, site):
        heights = [p**(height_exponents[t] - exponent) if t == top else 0 for t in tops]
        widths = [-int(j == site) for j in range(len(groups))]
        return heights + widths

    E, competitors = [], []
    for site, group in enumerate(groups):
        top, _, exponent, _ = group[0]
        E.append(active_row(top, exponent, site))
        for top, _, exponent, _ in group[1:]:
            competitors.append(active_row(top, exponent, site))

    modulus = p**C
    allowed = admissible_basis(competitors, len(tops) + len(groups), modulus)
    image = matrix_product(E, allowed)
    factors = smith_factors(image)
    # The shared heights contribute one new residue direction on the three
    # duplicated sites. These two primitive relations characterize its image.
    exponents = [row["i"] for row in reads]
    assert exponents == [1, 3, 5, 7] and tops == [1, p**2]
    for i in (1, 2):
        ratio = p**(exponents[-1] - exponents[i])
        assert all((u - ratio*v) % modulus == 0 for u, v in zip(image[i], image[-1]))
    assert factors == [1, 1, modulus, modulus]
    return {"height_increment_p_exponents_by_top": height_exponents,
            "smith_factors": factors, "quotient_length": 2*C,
            "unit_factors": 2, "competing_modulus": modulus}


def main():
    certify_host()
    check_stronger_size_band()
    # All exceptional first-return targets lie in TOPS; invert each positive site.
    excluded = sorted(r[:3] for h in TOPS for r in active_reads_at_site(0, h)
                      if r[3] == "first-excluded")
    assert excluded == [(1, 17, 1), (1, 47, 1)]
    # Brute trial division for this small 'first high' check, not for the full prefix.
    candidates = [p for p in range(33, 48) if power_of_prime(p) == (p, 1)]
    assert candidates == [37, 41, 43, 47]
    assert [classify(1, p, 1) for p in candidates] == [
        "non-Phi read zero", "non-Phi read zero", "retained", "first-excluded"]
    rows = {p: selected_width_rows(p) for p in (13, 43)}
    assert rows[13]["smith_exponents"] == [0] * 6
    assert rows[43]["smith_exponents"] == [0, C, C, C]
    assert all(r["other_reads_at_site"] == [(43**2, 43, r["i"] - 2, "retained")]
               for r in rows[43]["rows"][1:])
    for p, info in rows.items():
        info["direct_smith_in_original_and_changed_bases"] = recompute_width_image(p, info)
        # Increase this width from 16 to 17 for every u,j. ASK has one
        # physical 2 log(p) contribution per active preimage. MAIN averages
        # the logarithmic shift over all 2|H| positive sites, at every top.
        qnorm = Q(len(TOPS) * R * B, 2)
        phi_card = 2 * 2**E
        for row in info["rows"]:
            multiplicity = 1 + len(row["other_reads_at_site"])
            ask = -Q(R * 2 * multiplicity, qnorm)
            minus_main = Q(len(TOPS) * R * B * N, phi_card * qnorm)
            assert ask == -Q(multiplicity, 16) and minus_main == Q(N, 2**E)
            assert 0 < minus_main < 1 and p >= 13
            row["normalized_signed_width_change"] = {
                "log_p": str(ask), "log_17_over_16": str(minus_main)}
    rows[43]["free_top_heights_on_listed_active_reads"] = shifted_height_image(43, rows[43])
    primes = (2, 3, 5, 7, 11, 13, 17, 37, 41, 43, 47)
    print(json.dumps({
        "eps_WinPair_and_PageN": ["1/64", "9/560"],
        "eps_sharpened_PageN_band": "9/560",
        "geometric_size_windows": "fails top-density and 26 threshold", "R=m": R, "N=x=Y": N, "e": E, "q": Q_PRIME,
        "d_expression": "3814*5^400+1", "d_bit_length": D.bit_length(),
        "TT_dyadic_unit_representatives": TOPS, "T2": "all H", "Delta": 1,
        "b=beta=w": B, "h": 1, "a=Amax": B*N, "projection_divisor": len(TOPS)*R*B//2,
        "lattice_rank_over_ring_of_integers": R**3-1,
        "ramified_inertia_sizes": {"2": 2**E, "3": 2, "d": 2},
        "ramified_frobenius": {p: frobenius(p) for p in (2, 3, D)},
        "all_excluded_by_top_base_exponent": excluded,
        "excluded_normalized_terms_log_multipliers": {
            str(p): str(Q(N, p)-1) for _, p, _ in excluded},
        "first_three_powers_at_top_1": {p: [classify(1, p, i) for i in (1, 2, 3)] for p in primes},
        "partitions_per_base": {z: {p: ("low" if p <= z else "high") for p in primes}
                                for z in (16, 32)},
        "c": C, "actual_active_width_readouts": rows,
        "physical_section_and_dual_E_C": "unconstructed", "PairGood_bounds": "unverified"
    }, indent=2))


if __name__ == "__main__":
    main()
