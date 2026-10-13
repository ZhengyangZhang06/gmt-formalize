# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.local_multiplicity_one-a1.weight_restrict_eq-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-local-multiplicity-one-a1-weigh-1d13f27592/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.local_multiplicity_one-a1`
- Child key: `weight_restrict_eq`
- Declaration: `Submission.dohr_lmo_weight_restrict_eq`
- Exact Lean type: `∀ n ℓ : ℕ, ∀ (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (O : Set (Amb n ℓ)), MeasurableSet O → (∀ᵐ x ∂V.weight, x ∈ O → V.mult x = 1) → (μHE[n] : Measure (Amb n ℓ)) (symmDiff (V.carrier ∩ O) (V.support ∩ O)) = 0 → V.weight.restrict O = (μHE[n] : Measure (Amb n ℓ)).restrict (V.support ∩ O)`

## Sibling prerequisites

- `root.density_one_higher_regularity-a1.local_multiplicity_one-a1.hausdorff_null_of_weight_null-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
