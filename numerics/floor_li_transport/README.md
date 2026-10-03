# Floor-Li transport miner

This directory contains the finite \(10^8\) transport experiment documented in
\`research/VF_MID_FLOOR_LI_TRANSPORT_MINING.md\`.

Run:

\`\`\`bash
python numerics/floor_li_transport/run_transport_miner.py
\`\`\`

The script computes the actual-prime / floor-\(Li_2\) primitive mismatch,
monotone/FIFO relocation geometry, square-block backlog energy, and
scale-controlled feedback diagnostics.

The committed \`results_1e8.json\` is a finite diagnostic record only.  In
particular, the observed maximum relocation lifetime is not used as a theorem.
The relocation gap is reported in the script's
\(\lfloor\sqrt n\rfloor\) bin convention; exact half-open square-block endpoint
normalization should be applied before citing it as a literal block theorem.
