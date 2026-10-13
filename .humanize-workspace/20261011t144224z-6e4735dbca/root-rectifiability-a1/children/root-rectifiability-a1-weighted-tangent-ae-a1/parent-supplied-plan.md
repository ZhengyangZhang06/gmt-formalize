# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rectifiability-a1.weighted_tangent_ae-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-weighted-tangent-ae-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rectifiability-a1`
- Child key: `weighted_tangent_ae`
- Declaration: `Submission.rectifiability_weighted_tangent_ae`
- Exact Lean type: `∀ (P m : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ), IsOpen U → M ⊆ U → NullMeasurableSet M (μHE[m + 1] : Measure (Eucl P)) → CountablyRectifiable (m + 1) M → (∀ x ∈ M, 0 < θ x) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → IntegrableOn θ (M ∩ K) (μHE[m + 1] : Measure (Eucl P))) → ∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), ∃ V : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt (m + 1) M θ x V`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
