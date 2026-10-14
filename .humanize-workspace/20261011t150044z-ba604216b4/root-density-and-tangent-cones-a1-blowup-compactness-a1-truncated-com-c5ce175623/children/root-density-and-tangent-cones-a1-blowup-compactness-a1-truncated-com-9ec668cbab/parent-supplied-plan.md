# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.slice_limit-a1.level_null-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-truncated-com-9ec668cbab/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.truncated_compactness-a1.closure-a1.slice_limit-a1`
- Child key: `level_null`
- Declaration: `Submission.dtc_bc_tc_cl_sl_ae_level_set_null`
- Exact Lean type: `∀ (P : ℕ) (ν : Measure (Euclid P)) (f : Euclid P → ℝ), Measurable f → (∀ K : Set (Euclid P), IsCompact K → ν K < ∞) → ∀ᵐ t ∂(volume : Measure ℝ), ν {x | f x = t} = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
