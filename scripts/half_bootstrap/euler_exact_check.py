#!/usr/bin/env python3
"""Exact finite algebra checks for euler_response.md, using only the stdlib.

Scope: formal polynomial identities over the rationals, cleared-denominator
rational identities, exact affine fixed points, and response exponent/phase
bookkeeping. These are identities for all values of their formal variables,
subject to the stated nonzero-denominator or sign conditions. They are not
sample-based checks.

This program does NOT prove the angular prime partial-sum input, an infinite
Euler product identity, a bound on the actual physical source, a zero-free
region, or a bootstrap to 1/2. The signed-symbol derivation in the note remains
conditional on its explicitly stated arithmetic and analytic inputs.

Import run_checks() for an audit workflow. It returns a JSON-serializable
summary and raises AssertionError on failure. No third-party dependencies,
network calls, or Lean execution are used.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
import json
from typing import Iterable, Mapping


# A monomial is a sorted tuple of (variable name, nonnegative exponent) pairs.
# The empty tuple is the constant monomial. Sparse canonical normal forms make
# equality an exact coefficient comparison, rather than numerical evaluation.
Monomial = tuple[tuple[str, int], ...]
Scalar = int | Fraction


def _multiply_monomials(left: Monomial, right: Monomial) -> Monomial:
    exponents = dict(left)
    for variable, exponent in right:
        exponents[variable] = exponents.get(variable, 0) + exponent
    return tuple(sorted((name, degree) for name, degree in exponents.items() if degree))


class Polynomial:
    """A small exact multivariate polynomial ring over Fraction coefficients."""

    __slots__ = ("_terms",)

    def __init__(self, terms: Mapping[Monomial, Scalar] | None = None) -> None:
        normal: dict[Monomial, Fraction] = {}
        for monomial, coefficient in (terms or {}).items():
            if not isinstance(coefficient, (int, Fraction)):
                raise TypeError("Only exact integer/Fraction coefficients are allowed")
            names: set[str] = set()
            for name, degree in monomial:
                if not isinstance(name, str) or not name:
                    raise TypeError("Variable names must be nonempty strings")
                if name in names or not isinstance(degree, int) or degree <= 0:
                    raise ValueError("Monomials require unique variables and positive powers")
                names.add(name)
            canonical = tuple(sorted(monomial))
            value = normal.get(canonical, Fraction(0)) + Fraction(coefficient)
            if value:
                normal[canonical] = value
            else:
                normal.pop(canonical, None)
        self._terms = normal

    @classmethod
    def constant(cls, value: Scalar) -> Polynomial:
        if not isinstance(value, (int, Fraction)):
            raise TypeError("Floating-point constants are not permitted")
        return cls({(): Fraction(value)})

    @classmethod
    def variable(cls, name: str) -> Polynomial:
        return cls({((name, 1),): Fraction(1)})

    @staticmethod
    def coerce(value: Polynomial | Scalar) -> Polynomial:
        if isinstance(value, Polynomial):
            return value
        return Polynomial.constant(value)

    def __add__(self, other: Polynomial | Scalar) -> Polynomial:
        right = self.coerce(other)
        result = dict(self._terms)
        for monomial, coefficient in right._terms.items():
            result[monomial] = result.get(monomial, Fraction(0)) + coefficient
        return Polynomial(result)

    def __radd__(self, other: Polynomial | Scalar) -> Polynomial:
        return self + other

    def __neg__(self) -> Polynomial:
        return Polynomial({monomial: -value for monomial, value in self._terms.items()})

    def __sub__(self, other: Polynomial | Scalar) -> Polynomial:
        return self + -self.coerce(other)

    def __rsub__(self, other: Polynomial | Scalar) -> Polynomial:
        return self.coerce(other) - self

    def __mul__(self, other: Polynomial | Scalar) -> Polynomial:
        right = self.coerce(other)
        result: dict[Monomial, Fraction] = {}
        for left_monomial, left_value in self._terms.items():
            for right_monomial, right_value in right._terms.items():
                monomial = _multiply_monomials(left_monomial, right_monomial)
                result[monomial] = (
                    result.get(monomial, Fraction(0)) + left_value * right_value
                )
        return Polynomial(result)

    def __rmul__(self, other: Polynomial | Scalar) -> Polynomial:
        return self * other

    def __pow__(self, exponent: int) -> Polynomial:
        if not isinstance(exponent, int) or exponent < 0:
            raise TypeError("Polynomial powers must be nonnegative integers")
        result = Polynomial.constant(1)
        factor = self
        power = exponent
        while power:
            if power & 1:
                result = result * factor
            factor = factor * factor
            power //= 2
        return result

    def substitute(self, values: Mapping[str, Polynomial | Scalar]) -> Polynomial:
        result = Polynomial.constant(0)
        for monomial, coefficient in self._terms.items():
            term = Polynomial.constant(coefficient)
            for name, degree in monomial:
                replacement = self.coerce(values.get(name, Polynomial.variable(name)))
                term = term * replacement**degree
            result = result + term
        return result

    @property
    def is_zero(self) -> bool:
        return not self._terms

    def __repr__(self) -> str:
        return f"Polynomial({self._terms!r})"


@dataclass(frozen=True)
class AtomSignature:
    """Formal exponents before taking absolute values or averaging primes.

    An atom has the form
      (1-q)^one_minus_q * Q^q_power * eta^eta_power
        * lambda^angular_power * exp(-delay * log(Q) * s).

    Sign and binomial multiplicity are separate and are retained by the exact
    response recurrence checks. Signatures multiply by adding their entries.
    """

    q_power: Polynomial
    delay: Polynomial
    eta_power: Polynomial
    angular_power: Polynomial
    one_minus_q: Polynomial

    @classmethod
    def from_integers(cls, *entries: int) -> AtomSignature:
        if len(entries) != 5:
            raise ValueError("An atom signature has five components")
        return cls(*(Polynomial.constant(entry) for entry in entries))

    def components(self) -> tuple[Polynomial, ...]:
        return (
            self.q_power,
            self.delay,
            self.eta_power,
            self.angular_power,
            self.one_minus_q,
        )

    def __add__(self, other: AtomSignature) -> AtomSignature:
        return AtomSignature(*(a + b for a, b in zip(self.components(), other.components())))

    def scale(self, exponent: Polynomial | Scalar) -> AtomSignature:
        return AtomSignature(*(entry * exponent for entry in self.components()))


class Checks:
    def __init__(self) -> None:
        self.names: list[str] = []

    def identity(self, name: str, left: Polynomial | Scalar, right: Polynomial | Scalar) -> None:
        difference = Polynomial.coerce(left) - right
        if not difference.is_zero:
            raise AssertionError(f"{name}: nonzero polynomial difference: {difference!r}")
        self.names.append(name)

    def nonzero(self, name: str, polynomial: Polynomial) -> None:
        if polynomial.is_zero:
            raise AssertionError(f"{name}: expected a nonzero formal polynomial")
        self.names.append(name)

    def exact(self, name: str, condition: bool) -> None:
        if not condition:
            raise AssertionError(name)
        self.names.append(name)

    def positive_certificate(
        self,
        name: str,
        polynomial: Polynomial,
        nonnegative_variables: Iterable[str],
        positive_variables: Iterable[str] = (),
    ) -> None:
        """Verify a sufficient exact coefficient certificate for positivity.

        Every coefficient must be nonnegative, every variable must be in its
        declared sign domain, and at least one positive-coefficient monomial
        must use only strictly positive variables (a positive constant also
        qualifies). This proves positivity on the stated whole orthant.
        """
        positive = set(positive_variables)
        permitted = set(nonnegative_variables) | positive
        strictly_positive_term = False
        for monomial, coefficient in polynomial._terms.items():
            variables = {variable for variable, _ in monomial}
            if coefficient < 0 or not variables <= permitted:
                raise AssertionError(f"{name}: invalid positivity certificate {polynomial!r}")
            if coefficient > 0 and variables <= positive:
                strictly_positive_term = True
        if not strictly_positive_term:
            raise AssertionError(f"{name}: no term is provably strictly positive")
        self.names.append(name)


def run_checks() -> dict[str, object]:
    """Run exact identities; return scope-labelled results or raise on failure."""
    checks = Checks()
    var = Polynomial.variable
    q, R, D = (var(name) for name in ("q", "R", "D"))
    b, x, theta = (var(name) for name in ("b", "x", "theta"))
    r, j, ell, h, k = (var(name) for name in ("r", "j", "ell", "h", "k"))
    epsilon, delta = (var(name) for name in ("epsilon", "delta"))

    # Start from the source definition of markedFactor, rather than assuming
    # its simplified principal-slice value. P_num/P_den is its rational form
    # when V=W=q, K=(1-q)D, J=-D+qR. All equalities below are cross-products;
    # they therefore check cleared-denominator polynomial identities.
    K = (1 - q) * D
    J = -D + q * R
    P_num = R * (1 - q) - K * q + J * (1 - q)
    P_den = (1 - q) * (1 - R)
    checks.identity(
        "principal markedFactor simplification",
        P_num,
        (1 - q) * (1 + q) * (R - D),
    )

    # continuedCorrection = [1-q^2+(1-q)^2 P] / (1-D).
    C_num = (1 - q**2) * P_den + (1 - q) ** 2 * P_num
    C_den = P_den * (1 - D)
    U = 1 - q * R - (1 - q) * D

    E1_num = (1 - q**2) * U
    E1_den = (1 - R) * (1 - D)
    checks.identity("E1 correction factorization", C_num * E1_den, E1_num * C_den)

    E2_num = (1 - q**2) * ((1 - D) + q * (D - R))
    E2_den = 1 - D
    checks.identity(
        "E2 extracted correction",
        (1 - R) * C_num * E2_den,
        E2_num * C_den,
    )
    checks.identity(
        "E2 residual defect numerator",
        E2_num - E2_den,
        -q**2 * (1 - D) + (1 - q**2) * q * (D - R),
    )

    # The exact signed slot is S=q+(1-q)(1-R/D)/U, using B*D=1.
    # This substitution is valid for the actual unit target phase. No norm
    # bound or triangle inequality has been used in this grouping.
    S_num = q * D * U + (1 - q) * (D - R)
    S_den = D * U
    N_num = D - q**2 * R * D - q * (1 - q) * D**2 - (1 - q) * R
    E5_num = (1 - q**2) * N_num
    E5_den = D * (1 - R) * (1 - D)
    checks.identity(
        "E5 exact signed correction times slot",
        C_num * S_num * E5_den,
        E5_num * C_den * S_den,
    )
    E6_right = (1 - q) * (D - 1) * (1 - q * D)
    checks.identity("E6 numerator at R=1", N_num.substitute({"R": 1}), E6_right)
    checks.nonzero("E6 no formal cancellation by 1-R", E6_right)
    for name, denominator in (
        ("source marked denominator", P_den),
        ("source correction denominator", C_den),
        ("exact signed slot denominator", S_den),
    ):
        checks.nonzero(f"nonzero denominator polynomial: {name}", denominator)

    # F6 and the reflected map are checked by polynomial branch identities.
    # The exact rational evaluations confirm that both roots belong to their
    # selected max branch; branch factorization proves there are no others.
    F6 = Fraction(1, 6) * (b + 3)
    checks.identity("F6 fixed point identity", F6 - Fraction(3, 5), Fraction(1, 6) * (b - Fraction(3, 5)))
    checks.identity("folded direct fixed point polynomial", (6 * x - 3) - x, 5 * (x - Fraction(3, 5)))
    checks.identity("folded reflected fixed point polynomial", (4 - 6 * x) - x, -7 * (x - Fraction(4, 7)))
    checks.identity("folded branch crossing", (6 * x - 3) - (4 - 6 * x), 12 * (x - Fraction(7, 12)))
    checks.identity("folded absolute-value right branch", 6 * x - 3, Fraction(1, 2) + 6 * (x - Fraction(7, 12)))
    checks.identity("folded absolute-value left branch", 4 - 6 * x, Fraction(1, 2) + 6 * (Fraction(7, 12) - x))
    for fixed in (Fraction(4, 7), Fraction(3, 5)):
        folded = max(6 * fixed - 3, 4 - 6 * fixed)
        checks.exact(f"folded fixed point {fixed}", folded == fixed)
        checks.exact(f"fixed point {fixed} in open half-to-two-thirds interval", Fraction(1, 2) < fixed < Fraction(2, 3))

    F5 = Fraction(1, 5) * (b + 2)
    checks.identity("F5 half-centered recurrence", F5 - Fraction(1, 2), Fraction(1, 5) * (b - Fraction(1, 2)))
    checks.identity("F5 strict improvement amount", b - F5, Fraction(4, 5) * (b - Fraction(1, 2)))
    checks.identity("desired half-centered F6", Fraction(1, 6) * (b + Fraction(5, 2)) - Fraction(1, 2), Fraction(1, 6) * (b - Fraction(1, 2)))

    # The angular orbit formula is checked as an induction schema: t stands
    # for 6^n, so replacing t by 6t is precisely the next step for every n.
    t = var("t")
    direct_angle = Fraction(6, 5) * (1 - t)
    checks.identity("direct angular orbit initial value", direct_angle.substitute({"t": 1}), 0)
    checks.identity("direct angular orbit induction", direct_angle.substitute({"t": 6 * t}), 6 * direct_angle - 6)
    checks.identity("functional dual angular map", -(6 * ell - 6), 6 - 6 * ell)

    # Verify the full finite-response formula by its base and recurrence,
    # rather than checking a finite list of truncation orders. G denotes the
    # arbitrary previous geometric sum, G_next=1+H*G.
    H, W, G, p, tail = (var(name) for name in ("H", "W", "G", "p", "tail"))
    response = (1 - q) * ((G - 1) - W * G)
    checks.identity("S1 response base K=0", response.substitute({"G": 1}), -(1 - q) * W)
    checks.identity(
        "S1 response induction schema for every K",
        response.substitute({"G": 1 + H * G}),
        -(1 - q) * W + H * ((1 - q) + response),
    )
    checks.identity("complete mixed-slot product recursion", 1 + p + tail + p * tail, (1 + p) * (1 + tail))

    # Derive atoms from the original source coordinates. B has delay -1 and
    # eta exponent -1 because |eta|=1, so B=eta^(-1)*Q^s.
    atom_R = AtomSignature.from_integers(3, 6, 6, -6, 0)
    atom_q = AtomSignature.from_integers(-1, 0, 0, 0, 0)
    atom_D = AtomSignature.from_integers(0, 1, 1, 0, 0)
    atom_B = AtomSignature.from_integers(0, -1, -1, 0, 0)
    outer = AtomSignature.from_integers(0, 0, 0, 0, 1)
    atom_W = atom_R + atom_B
    atom_qR = atom_q + atom_R
    atom_Dbranch = atom_D + outer
    monomial = outer + atom_W + atom_qR.scale(r) + atom_Dbranch.scale(j)
    expected = AtomSignature(
        2 * r + 3,
        6 * r + j + 5,
        6 * r + j + 5,
        -6 * (r + 1),
        j + 1,
    )
    component_names = ("Q coefficient power", "delay multiplier", "finite character power", "angular phase power", "one-minus-q multiplicity")
    for name, actual, required in zip(component_names, monomial.components(), expected.components()):
        checks.identity(f"W H^k monomial: {name}", actual, required)

    angular_type = monomial.angular_power + monomial.eta_power * ell
    checks.identity("angular target substitution", angular_type, (6 * r + j + 5) * ell - 6 * (r + 1))
    angular_div_six = (6 * r + j + 5) * h - (r + 1)
    checks.identity("angle on ell=6h", angular_type.substitute({"ell": 6 * h}), 6 * angular_div_six)
    # Integer h obeys h<=0 or h>=1. Set h=-k or h=1+k with k>=0.
    # Strict positivity of the resulting polynomial proves the angular type
    # is nonzero for every r,j>=0 and every ell in 6Z, without finite sampling.
    checks.positive_certificate("W-family angle nonzero for h<=0", -angular_div_six.substitute({"h": -k}), ("r", "j", "k"))
    checks.positive_certificate("W-family angle nonzero for h>=1", angular_div_six.substitute({"h": 1 + k}), ("r", "j", "k"))

    # The residue weight contributes -5/6 and the actual mass has power
    # 1-5/6=1/6. The prime-input exponent b replaces the raw counting power 1.
    # A logarithm is absorbed into an explicit positive loss in the note;
    # this program checks powers, not that analytic absorption or prime input.
    residue_weight = Fraction(-5, 6)
    mass_power = Fraction(1) + residue_weight
    checks.exact("original residue mass power", mass_power == Fraction(1, 6))
    raw_weighted_exponent = b + monomial.q_power - theta * monomial.delay + residue_weight + epsilon
    checks.identity(
        "original weighted W numerator exponent",
        raw_weighted_exponent,
        b + 2 * r + Fraction(13, 6) - (6 * r + j + 5) * theta + epsilon,
    )
    normalized_exponent = raw_weighted_exponent - mass_power
    checks.identity(
        "original normalized W monomial exponent",
        normalized_exponent,
        b + 2 + 2 * r - (6 * r + j + 5) * theta + epsilon,
    )
    checks.identity(
        "W monomial relative to its leading atom",
        normalized_exponent - (b + 2 - 5 * theta + epsilon),
        r * (2 - 6 * theta) - j * theta,
    )
    checks.identity("unmarked H monomial exponent", (atom_qR.scale(r) + atom_Dbranch.scale(j)).q_power - theta * (atom_qR.scale(r) + atom_Dbranch.scale(j)).delay, 2 * r - (6 * r + j) * theta)
    u = var("u")
    checks.positive_certificate("extra qR improves exponent for theta>1/2", (6 * theta - 2).substitute({"theta": Fraction(1, 2) + u}), (), ("u",))
    checks.positive_certificate("extra D improves exponent for theta>1/2", theta.substitute({"theta": Fraction(1, 2) + u}), (), ("u",))

    # Show that all three exponents used in kappa are positive on the
    # conditional F5 domain. This is an exact positivity certificate, not an
    # analytic assertion that the input boundary or prime estimate holds.
    domain = {
        "b": Fraction(1, 2) + h,
        "theta": Fraction(1, 2) + Fraction(1, 5) * h + Fraction(1, 5) * (epsilon + delta),
    }
    marked_decay = (5 * theta - b - 2 - epsilon).substitute(domain)
    checks.identity("F5 threshold including explicit loss", marked_decay, delta)
    for name, expression in (
        ("theta", theta),
        ("6theta-2", 6 * theta - 2),
        ("5theta-b-2-loss", 5 * theta - b - 2 - epsilon),
    ):
        checks.positive_certificate(
            f"conditional kappa positivity: {name}",
            expression.substitute(domain),
            ("epsilon",),
            ("h", "delta"),
        )

    return {
        "status": "PASS",
        "check_count": len(checks.names),
        "checks": checks.names,
        "arithmetic": "stdlib Fraction coefficients and canonical sparse polynomial normal forms",
        "identity_scope": "finite formal identities; rational equalities on their nonzero-denominator domains",
        "not_proved": [
            "angular prime partial-sum or original mass inputs",
            "infinite Euler product identification or analytic continuation",
            "physical LOW/HIGH return estimates or numerator noncancellation",
            "a zero-free bound, RH, or a complete bootstrap to one half",
        ],
    }


if __name__ == "__main__":
    print(json.dumps(run_checks(), indent=2))
