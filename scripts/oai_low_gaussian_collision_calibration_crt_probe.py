#!/usr/bin/env python3
"""Finite CRT sanity audit with actual calibration residue-field types.

Ramified lambda has residue F3; inert 2 has residue F4.
The good split s=7 is a PRINCIPAL mask in the s|I collision.
Good split I'=13 contributes a primitive sextic exponent 4;
good split J-only=37 carries the principal mask from even cubic
exponent. These are finite local-field probes, not the complete
Eisenstein detector or proof of a global energy bound.
"""
from cmath import exp, pi
from math import isclose, sqrt


def fft(n, chi, psi):
    return [sum(chi(x) * psi(k, x) for x in range(n))
            for k in range(n)]


def f4_mul(x, y):
    """F2[w]/(w^2+w+1), bit representation a + b*w."""
    a, b = x & 1, (x >> 1) & 1
    c, d = y & 1, (y >> 1) & 1
    return ((a*c + b*d) & 1) | (((a*d+b*c+b*d) & 1) << 1)


def calibration_fourier():
    zeta3 = exp(2j*pi/3)
    chi4 = lambda x: (0j if x == 0 else
                       {1: 1+0j, 2: zeta3, 3: zeta3**2}[x])
    # Tr_4/2(a+b*w)=b.
    psi4 = lambda k, x: (-1) ** (f4_mul(k, x) >> 1)
    F4 = fft(4, chi4, psi4)
    chi3 = lambda x: 0j if x == 0 else (1+0j if x == 1 else -1+0j)
    F3 = fft(3, chi3, lambda k, x: exp(2j*pi*k*x/3))
    return F4, F3


def principal_prime_fourier(p):
    return fft(p, lambda x: 1+0j if x else 0j,
               lambda k, x: exp(2j*pi*k*x/p))


def column_sextic_fourier(p=13, exponent=4, g=2):
    logs, power = {}, 1
    for k in range(p-1):
        logs[power] = k
        power = (power*g) % p
    assert len(logs) == p-1
    return fft(p, lambda x: 0j if x == 0 else
               exp(2j*pi*exponent*logs[x]/6),
               lambda k, x: exp(2j*pi*k*x/p))


def approx(a, b, tol=1e-8):
    assert isclose(a, b, rel_tol=tol, abs_tol=tol), (a, b)


def main():
    F4, F3 = calibration_fourier()
    S7 = principal_prime_fourier(7)
    J37 = principal_prime_fourier(37)
    I13 = column_sextic_fourier()

    for name, F, maximum, zero in [
        ("calibration F4", F4, 2, 0),
        ("calibration F3", F3, sqrt(3), 0),
        ("collision principal s7", S7, 6, 6),
        ("good I-prime 13 exponent 4", I13, sqrt(13), 0),
        ("even J-prime 37 principal", J37, 36, 36)]:
        approx(max(abs(v) for v in F), maximum)
        approx(abs(F[0]), zero)
        print(name, "zero=", round(abs(F[0]), 9),
              "max=", round(max(abs(v) for v in F), 9))

    # I=s, J square: no genuine primitive s or J phase.
    # Calibration still kills the zero mode; the energy does NOT vanish.
    combined_zero = abs(F4[0]*F3[0]*S7[0]*J37[0])
    approx(combined_zero, 0)
    coherent_energy = (4-1)*(3-1)*(7-1)*(37-1)
    assert coherent_energy == 1296
    print("coherent s/J zero =", combined_zero, "energy =", coherent_energy)
    print("without calibration, principal zero =", abs(S7[0]*J37[0]))
    approx(abs(S7[0]*J37[0]), 216)

    # With squarefree I'=13, local exponent 4 remains primitive;
    # no overlap leak, finite-CRT Fourier = product up to frequencies.
    max_product = 1.0
    for F in (F4, F3, S7, I13, J37):
        max_product *= max(abs(v) for v in F)
    upper = 7*37*sqrt(4*3*13)
    assert max_product <= upper + 1e-8
    approx(max_product, 6*36*sqrt(4*3*13))
    print("collision I'=13 max =", max_product, "bound =", upper)
    print("PASS: calibrated zero mode, original principal slot mask,"
          " primitive-column norm and nonzero squared energy")


if __name__ == "__main__":
    main()
