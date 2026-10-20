#!/usr/bin/env python3
"""All-integer original-square-block to quadratic/Eisenstein coefficient audit.

No native analytic character-moment estimate is claimed. This checks:
  mu_Z(n) == (chi_{-3} * a_F)(n), EVERY 1<=n<=1028^2-1;
  each 317/1027 prefix and the EXACT 317/1027 square-block boundaries;
  explicit signed off-diagonal pair summation (not independent signs);
  split-prime a_F(pq)=4 versus the original mu_Z(pq)=+1.
  original period-36 (1,3,4,12) full-norm square-boundary reassembly.

The coefficient a_F uses the exact local Euler polynomial:
    (1-t)(1-chi_{-3}(p)*t)
for every rational prime, retaining split / inert / ramified / p^2.
The actual Eisenstein IDEAL phase rows are checked separately by the
existing vf919_native_sextic_317_1027.py. Norm coefficients alone
must NOT be confused with the sextic prime-ideal character.
"""

def complete_mu(N):
    least = [0] * (N + 1)
    mu = [0] * (N + 1)
    mu[1] = 1
    primes = []
    for n in range(2, N + 1):
        if not least[n]:
            least[n] = n
            mu[n] = -1
            primes.append(n)
        for p in primes:
            if p > least[n] or n * p > N:
                break
            least[n * p] = p
            if p == least[n]:
                mu[n * p] = 0
                break
            mu[n * p] = -mu[n]
    return least, mu


def complete_norm_coefficients(least):
    """True rational Euler coefficient a_F = mu_Z * (chi_-3 * mu_Z)."""
    N = len(least) - 1
    a = [0] * (N + 1)
    a[1] = 1
    for n in range(2, N + 1):
        p = least[n]
        m = n
        e = 0
        while m % p == 0:
            m //= p
            e += 1
        if p == 3:
            local = -1 if e == 1 else 0
        elif p % 3 == 1:
            local = -2 if e == 1 else 1 if e == 2 else 0
        else:
            local = -1 if e == 2 else 0
        a[n] = local * a[m]
    return a


def reconstruct_all_mu(a):
    """Reconstruct the full Dirichlet convolution at each physical n."""
    N = len(a) - 1
    recovered = [0] * (N + 1)
    for d in range(1, N + 1):
        r = d % 3
        if r == 0:
            continue
        chi = 1 if r == 1 else -1
        for e in range(1, N // d + 1):
            recovered[d * e] += chi * a[e]
    return recovered


def audit_interval(title, a, b, true_mu, recovered, expected):
    # Half-open physical interval; square shells retain a=R^2 and exclude
    # b=(R+1)^2, as in the Lean theorem.
    w = recovered[a:b]
    assert w == true_mu[a:b], title
    mass = sum(w)
    diagonal = sum(v*v for v in w)
    # EXPLICIT m<n: no recursion or independence shortcut here.
    covariance = sum(w[j] * w[i]
                     for j in range(len(w))
                     for i in range(j))
    assert (mass, diagonal, covariance) == expected, (
        title, mass, diagonal, covariance, expected)
    assert mass * mass == diagonal + 2 * covariance
    print(f"{title}: [{a},{b}), sites={len(w)}, M={mass}, "
          f"K={diagonal}, C={covariance}, K+2C={diagonal+2*covariance}")



def q36(t):
    """Native period-36 restored Euler character/floor kernel."""
    c = lambda k: int(k % 3 == 1)
    return c(t) - c(t // 3) - c(t // 4) + c(t // 12)


def periodic_excluded_norm_prefix(X, norm_coeff):
    """Exactly vf919OAIExcludedNormSharpPrefix(X), not an Mertens shortcut."""
    return sum(norm_coeff[m] * q36(X // m)
               for m in range(1, X + 1)
               if m % 2 and m % 3)


def audit_periodic_double_square_boundary(R, norm_coeff, mu, expected):
    lo = R * R - 1
    hi = (R + 1) ** 2 - 1
    mlo = periodic_excluded_norm_prefix(lo, norm_coeff)
    mhi = periodic_excluded_norm_prefix(hi, norm_coeff)
    assert (mlo, mhi) == expected, (R, mlo, mhi, expected)
    assert (mlo, mhi) == (sum(mu[1:lo+1]), sum(mu[1:hi+1]))
    print(f"R={R} periodic36: M({lo})={mlo}, M({hi})={mhi}, "
          f"true sharp shell increment={mhi-mlo}")

def main():
    N = 1028 ** 2 - 1
    least, mu = complete_mu(N)
    norm_coeff = complete_norm_coefficients(least)
    recovered = reconstruct_all_mu(norm_coeff)
    assert recovered[1:] == mu[1:], "incomplete integer-by-integer source"
    for n in (133, 259, 100531, 1054741):
        assert norm_coeff[n] == 4
        assert recovered[n] == mu[n] == 1
    # The full split-prime four-term quadratic-convolution payment at n=133.
    assert (norm_coeff[133], norm_coeff[19], norm_coeff[7], norm_coeff[1]) == (
        4, -2, -2, 1)
    assert 4 - 2 - 2 + 1 == mu[133] == 1

    audit_interval("X=317 complete prefix", 1, 318,
                   mu, recovered, (-4, 194, -89))
    audit_interval("X=1027 complete prefix", 1, 1028,
                   mu, recovered, (-3, 625, -308))
    audit_interval("R=317 original square block", 317**2, 318**2,
                   mu, recovered, (11, 387, -133))
    audit_interval("R=1027 original square block", 1027**2, 1028**2,
                   mu, recovered, (-20, 1252, -426))
    audit_periodic_double_square_boundary(317, norm_coeff, mu, (-28, -17))
    audit_periodic_double_square_boundary(1027, norm_coeff, mu, (367, 347))
    print("PASS: every original Mobius coefficient through 1028^2-1; "
          "original complete ordered covariance at 317/1027 "
          "and both 317/1027 square blocks")


if __name__ == "__main__":
    main()
