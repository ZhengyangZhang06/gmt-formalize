# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_any_radius-a1.patching-a1.op_norm_le_hs_norm-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-patching-a1-op-norm-le-hs-norm-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_any_radius-a1.patching-a1`
- Child key: `op_norm_le_hs_norm`
- Declaration: `Submission.arp_opNorm_le_hsNorm`
- Exact Lean type: `∀ {m k : ℕ} (A : Rn m →L[ℝ] Rn k), ‖A‖ ≤ hsNorm A`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
