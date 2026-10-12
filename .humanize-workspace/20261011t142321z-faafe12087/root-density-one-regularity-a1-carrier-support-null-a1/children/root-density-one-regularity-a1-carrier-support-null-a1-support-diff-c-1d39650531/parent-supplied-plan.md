# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_regularity-a1.carrier_support_null-a1.support_diff_carrier_null-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-regularity-a1-carrier-support-null-a1-support-diff-c-1d39650531/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_regularity-a1.carrier_support_null-a1`
- Child key: `support_diff_carrier_null`
- Declaration: `Submission.hausdorff_support_diff_carrier_null`
- Exact Lean type: `∀ {n ℓ : ℕ} {U : Set (Amb n ℓ)} (V : RectifiableVarifold n ℓ U), (∀ x ∈ V.support, ∃ t : ℝ, 0 < t ∧ V.HasDensity x t) → (μHE[n] : Measure (Amb n ℓ)) (V.support \ V.carrier) = 0`

## Sibling prerequisites

- `root.density_one_regularity-a1.carrier_support_null-a1.upper_density_null-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
