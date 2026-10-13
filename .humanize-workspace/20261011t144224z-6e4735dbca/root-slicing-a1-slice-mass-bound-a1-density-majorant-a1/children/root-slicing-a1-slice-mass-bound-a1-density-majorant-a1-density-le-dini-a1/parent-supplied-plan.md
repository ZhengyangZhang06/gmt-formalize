# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_mass_bound-a1.density_majorant-a1.density_le_dini-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-density-majorant-a1-density-le-dini-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_mass_bound-a1.density_majorant-a1`
- Child key: `density_le_dini`
- Declaration: `Submission.slicing_mb_dm_density_le_lowerLeftDini`
- Exact Lean type: `∀ (ν : Measure ℝ) (a b : ℝ), ν (Ioo a b) ≠ ∞ → ∀ t ∈ Ioo a b, liminf (fun h : ℝ => ν (Icc (t - h) t) / ENNReal.ofReal h) (𝓝[>] 0) ≤ liminf (fun k : ℝ => ENNReal.ofReal (((ν (Ioo a b ∩ Iic t)).toReal - (ν (Ioo a b ∩ Iic (t - k))).toReal) / k)) (𝓝[>] 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
