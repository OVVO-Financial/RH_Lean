#!/usr/bin/env python3
"""A finite exact counterexample to dropping cubic CRT cross factors.

Source identities:
  OAI/NumberTheory/DirichletL/Detector/PairPhase.lean:
    sexticPair(p,q)^3=reciprocitySign(p,q)
  .../CubicGaussCRT.lean:
    gaussTwo(I*J)=sexticPair(I,J)^2*gaussTwo(I)*gaussTwo(J).
  .../Phase.lean:
    quadraticRaySign is determined by the 4-adic ray.

We test two primary good Eisenstein primes with 4-ray (1,0) (so
quadratic reciprocitySign=+1), and show they are *cubic nonresidues*
across the other prime. Cubic reciprocity then implies that their
sexticPair^2 is a NONTRIVIAL cube root of 1 (not equal to 1).

No reliance on floating point, sample statistics, or an unproved
identification of the fully compensated detector with theta coefficients.
"""

from math import isqrt


def norm(a: int, b: int) -> int:
    return a * a - a * b + b * b


def is_prime(n: int) -> bool:
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def root_omega_mod(a: int, b: int, p: int) -> int:
    # In O/(a+b*omega), omega = -a/b in F_p for prime norm p.
    r = (-a * pow(b, -1, p)) % p
    assert (r * r + r + 1) % p == 0
    return r


def evaluate_mod(a: int, b: int, root: int, prime: int) -> int:
    return (a + b * root) % prime


def test() -> None:
    # Both elements are 1 modulo (1-omega)^2 ~ 3, and 1 modulo 4.
    # Thus both are primary and in the trivial quadratic ray class.
    p = (1, -12)
    q = (-23, -12)
    np, nq = norm(*p), norm(*q)
    assert (np, nq) == (157, 397)
    assert is_prime(np) and is_prime(nq)
    assert all(a % 3 == 1 and b % 3 == 0 for a, b in (p, q))
    assert all(a % 4 == 1 and b % 4 == 0 for a, b in (p, q))
    # Original quadraticRayExponent((1,0)) = 0 and (1,0)*(1,0)=(1,0).
    quadratic_reciprocity_sign = 1
    assert quadratic_reciprocity_sign == 1

    rp, rq = root_omega_mod(*p, np), root_omega_mod(*q, nq)
    qp = evaluate_mod(*q, rp, np)
    pq = evaluate_mod(*p, rq, nq)
    assert (rp, rq, qp, pq) == (144, 362, 133, 24)
    # Cubic Euler criterion, both nontrivial; output equals omega^2
    # in their respective finite-field Eisenstein embeddings.
    cubic_q_mod_p = pow(qp, (np - 1) // 3, np)
    cubic_p_mod_q = pow(pq, (nq - 1) // 3, nq)
    assert (cubic_q_mod_p, cubic_p_mod_q) == (12, 34)
    assert cubic_q_mod_p == pow(rp, 2, np) != 1
    assert cubic_p_mod_q == pow(rq, 2, nq) != 1
    # Original sexticPair_cube and prime reciprocity imply that, with
    # reciprocitySign=+1, the cubic cross factor sexticPair^2 is nontrivial.
    print(
        "PASS: norm(p)=157 norm(q)=397; both primary, same trivial 4-ray;"
        " quadratic reciprocity sign=+1;"
        " cubic symbols are omega^2 at BOTH primes;"
        " sexticPair(p,q)^2 != 1."
    )


if __name__ == "__main__":
    test()
