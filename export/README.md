# Public repository export

`public-repo/` is the complete copy-ready seed for the new paper-facing repository.

The directory is intentionally separated from the broader `RH_Lean` sandbox. Copy **the contents of** `public-repo/`, not the enclosing `export/` directory, into the root of the new repository.

The formal theorem sources are a curated standalone import closure. Arithmetic and Fourier proof modules reuse the exact blobs merged in PRs #167 and #168; only the two public bridge adapters and the final public endpoint are newly isolated from sandbox dependencies.
