#!/usr/bin/env python3
"""Regression guard for #915: distinguish native recursive Sector Six from the
one-block VF-weighted oriented boundary. This is NOT an RH proof.

Native admitted/admitted #903 recursive Sector Six fails the cone at R=8,18.
The sampled complete #915 VF active-pair boundary lies inside the cone, but
is NOT a fully matched, occurrence-preserving recursively descended child run.
"""
import math
from vf_mid_sector_six_direct_probe import Arithmetic, sector_six_903, returned_weighted_915


def near(actual, expected, tol=1e-8):
    assert math.isclose(actual, expected, abs_tol=tol, rel_tol=tol), (
        actual, expected
    )


def main():
    a = Arithmetic(10500)

    # Exact finite-carrier counterexamples to the proposed blanket invariant.
    r8 = sector_six_903(a, 8, 8 ** 2 - 1)
    t8 = r8["recursive_sector_six_total"]
    assert t8["count"] == 1, t8
    near(t8["U"], 1)
    near(t8["L"], 0)
    near(t8["B"], -1)
    assert not t8["cone"]

    r18 = sector_six_903(a, 18, 18 ** 2 - 1)
    t18 = r18["recursive_sector_six_total"]
    assert t18["count"] == 106, t18
    near(t18["U"], 320 / 3)
    near(t18["L"], 46 / 3)
    near(t18["B"], -16196 / 9)
    assert not t18["cone"]
    print("#903 raw Sector Six: negative cone slack at R=8 and R=18 (expected).")

    # The actual VF returned active source is a DIFFERENT carrier.
    expected = {
        17: (38, 50, 17, 105),
        32: (84, 172, 44, 300),
        56: (330, 571, 89, 990),
        101: (1020, 2021, 280, 3321),
    }
    for R, (first, next_, returned, count) in expected.items():
        row = returned_weighted_915(a, R)
        boundary = row["six_oriented_boundary"]
        assert boundary["first_left"]["count"] == first, R
        assert boundary["next_right"]["count"] == next_, R
        assert boundary["returned_left"]["count"] == returned, R
        for forbidden in (
            "first_right", "next_left", "returned_right", "completed"
        ):
            assert boundary[forbidden]["count"] == 0, (R, forbidden)
        total = row["recovered_parent_fubini"]
        assert total["count"] == count, R
        assert total["cone"], (R, total)
        assert total["B"] > 0, (R, total)
        assert row["max_retained_weight_weld_error"] <= 1e-9
        near(
            total["signed"], row["reconstruction_closed_signed"], 1e-6
        )
        print(
            f"#915 R={R}: complete active source balanced; "
            f"U={total['U']:.6f}, L={total['L']:.6f}; "
            "retained-weight Fubini passes."
        )

    print("PASS: counterexamples and complete-VF sampled-carrier checks hold.")
    print("UNPROVED: initial anchored-cone payment and actual matched child-run "
          "cone preservation at all scales.")


if __name__ == "__main__":
    main()
