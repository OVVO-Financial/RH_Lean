#!/usr/bin/env python3
"""Compatibility entrypoint for the corrected dynamic Viole experiment.

The previous implementation used

    log b(x) = 2 + a/log(x) + b/log(x)^2,

which forced the unintended asymptotic base e^2. The canonical experiment now
uses a leading constant of 1 so that b(x) -> e.
"""

from vf_dynamic_e_asymptote_test import main


if __name__ == "__main__":
    main()
