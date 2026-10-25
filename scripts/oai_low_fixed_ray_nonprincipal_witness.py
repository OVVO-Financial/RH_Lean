#!/usr/bin/env python3
"""Exact finite primary Eisenstein witness: low column is nonconstant on a ray.

For minimal excluded prime set {lambda, (2)}, calibration generator g
has ideal (2*(1-omega)), with six unit associates. The two supported
primary split-prime elements n7=-2-3 omega and n139=10-3 omega are
congruent modulo g (difference 12), same physical ray modulo 4, and
their sextic symbols (g/n) differ for EVERY associate g.

Hence any calibration residueMonoid mod g takes the same value on
these elements, while idealRowHom(g,(n)) is different. This is finite
evidence for nontriviality of the periodic Gaussian column character
on the kernel of the ray projection. It does NOT prove that the
weighted global exceptional Gram is power-saving.

No third-party imports, exact integer modular arithmetic only.
"""


def eisenstein_mul(x, y):
    a, b = x
    c, d = y
    return (a*c-b*d, a*d+b*c-b*d)


def norm(z):
    a, b = z
    return a*a-a*b+b*b


def sextic_symbol_exponent(prime_generator, numerator):
    p = norm(prime_generator)
    a, b = prime_generator
    w = (-a * pow(b % p, -1, p)) % p
    root6 = (1+w) % p
    assert pow(root6, 6, p) == 1
    assert all(pow(root6, k, p) != 1 for k in (1,2,3))
    residue = (numerator[0]+w*numerator[1]) % p
    assert residue != 0
    sixth = pow(residue, (p-1)//6, p)
    matches = [k for k in range(6) if pow(root6,k,p)==sixth]
    assert len(matches)==1
    return matches[0]


def main():
    n7 = (-2,-3)
    n139 = (10,-3)
    assert (norm(n7), norm(n139)) == (7,139)
    assert all((n[0] % 3,n[1] % 3) == (1,0) for n in (n7,n139))
    assert tuple(a%4 for a in n7)==tuple(a%4 for a in n139)==(2,1)
    assert (n139[0]-n7[0],n139[1]-n7[1])==(12,0)
    g=(2,-2)  # 2*(1-omega)
    assert norm(g)==12
    assert eisenstein_mul(g,(4,2))==(12,0)
    units=((1,0),(-1,0),(0,1),(0,-1),(1,1),(-1,-1))
    differences=[]
    for u in units:
        gu=eisenstein_mul(g,u)
        assert norm(gu)==12
        e7=sextic_symbol_exponent(n7,gu)
        e139=sextic_symbol_exponent(n139,gu)
        diff=(e139-e7)%6
        assert diff!=0,(u,e7,e139)
        differences.append(diff)
        print(f"unit={u} generator={gu} chi_7={e7} "
              f"chi_139={e139} difference={diff} (mod 6)")

    assert sorted(differences)==[1,1,3,3,5,5]
    print("PASS: distinct same-ray low column characters for ALL six "
          "calibration generators of (2*lambda).")
    print("The actual weighted Gram and signed sixth-seed sum remain open.")


if __name__=="__main__":
    main()
