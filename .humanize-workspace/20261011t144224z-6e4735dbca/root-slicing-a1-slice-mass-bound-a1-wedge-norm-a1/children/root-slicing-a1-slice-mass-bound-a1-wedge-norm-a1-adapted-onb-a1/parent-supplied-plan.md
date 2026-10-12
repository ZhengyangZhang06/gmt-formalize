# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_mass_bound-a1.wedge_norm-a1.adapted_onb-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-wedge-norm-a1-adapted-onb-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_mass_bound-a1.wedge_norm-a1`
- Child key: `adapted_onb`
- Declaration: `Submission.slicing_mb_wn_adapted_onb`
- Exact Lean type: `∀ (P : ℕ) (α : Eucl P →L[ℝ] ℝ), ∃ u : OrthonormalBasis (Fin P) ℝ (Eucl P), ∀ j : Fin P, α (u j) = if (j : ℕ) = 0 then ‖α‖ else 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
