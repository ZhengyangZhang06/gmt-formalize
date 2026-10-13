# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_mass_bound-a1.density_majorant-a1.dini_lintegral_le-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-density-majorant-a1-dini-lintegral-le-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_mass_bound-a1.density_majorant-a1`
- Child key: `dini_lintegral_le`
- Declaration: `Submission.slicing_mb_dm_lintegral_lowerLeftDini_le`
- Exact Lean type: `∀ G : ℝ → ℝ, Monotone G → ∀ a b : ℝ, a ≤ b → ∫⁻ t in Ioo a b, liminf (fun k : ℝ => ENNReal.ofReal ((G t - G (t - k)) / k)) (𝓝[>] 0) ≤ ENNReal.ofReal (G b - G a)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
