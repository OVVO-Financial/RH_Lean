# Fixed-x prime population cutoff experiment

This directory reproduces the [research note](../../research/SEQUENTIAL_PRIME_POPULATION_CUTOFF_AND_ANCESTRY_2026_10_11.md). It implements the **actual** ordered-prime animation (candidate seed +1 at 1, -1 elsewhere, selected prime-square kills and later distinct-prime flips), not an independence model. The smooth-only Euler population is also recorded separately.

## Run

Use Python 3.10 or later, with NumPy, pandas and matplotlib.

~~~sh
python3 -m pip install -r scripts/PrimePopulationCutoff/requirements.txt
python3 scripts/PrimePopulationCutoff/prime_cutoff_audit.py
python3 scripts/PrimePopulationCutoff/prime_ancestry_cutoff.py
python3 scripts/PrimePopulationCutoff/all_square_endpoint_shared_ancestry.py
python3 scripts/PrimePopulationCutoff/all_square_overlap_crossings.py
python3 scripts/PrimePopulationCutoff/make_prime_cutoff_figures.py
~~~

Generated CSVs, JSON and PNGs are written next to the scripts unless the --outdir option is supplied. Default fixed endpoints: 30, 210, 288, **317**, 1023, **1027**, 3135, 9999, 100488, and 999999. Check the first negative post-root correction with:

~~~sh
python3 scripts/PrimePopulationCutoff/prime_cutoff_audit.py --values 9024 9214 9215 9216 9408
~~~

Outputs include prime_steps_x317.csv, prime_steps_x1027.csv, cutoff_summary.csv, ancestry_prefix_x1027.csv, all_square_roots_2_1000.csv, and all_square_shared_overlap_cutoffs_2_1000.csv.

## Exact identity audits

For every fresh active prime above the square root, the prime-candidate increment is
\[
\Delta_p=2(1-M(\lfloor x/p\rfloor)).
\]
For \(x/3<p\le x/2\), \(\Delta_p=2\) from the sole composite child \(2p\). Primes \(p>x/2\) are inert in the candidate frame.

Cofactor pairs with shared large-prime extension sets are weighted by
\[
N_{x,y}(d)=\#\{p\text{ prime}:\lfloor\sqrt x\rfloor<p\le y,\ p\le\lfloor x/d\rfloor\}.
\]
The ancestry script checks exactly
\[
\sum_p(M(\lfloor x/p\rfloor)-1)^2
 =D_{x,y}+2S_{x,y}+2B_{x,y},
\]
where \(S\) is signed shared-gcd overlap, \(B\) signed coprime overlap and \(D\) the diagonal.

The all-square-root script independently checks this through \(R=1000\). The earlier cofactor-conditioned full-root census through \(R=6000\) cross-checks the completed shared overlap; it counts **ordered** pairs and reports twice our **unordered** overlap.

## Proof status

All numerical results are finite and exact within their range. The completed negative shared-overlap pattern through R=6000 is **not** an all-root theorem, and by itself does not establish bounded coherent prime-insertion sums. There is no proof of finite C, finite A, or RH.