# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tangent_characterizations-a1.weighted_measure_properties-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-tangent-characterizations-a1-weighted-measure-properties-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tangent_characterizations-a1`
- Child key: `weighted_measure_properties`
- Declaration: `Submission.weightedMeasure_finite_null_tangent`
- Exact Lean type: `∀ (n N : ℕ) (M : Set (Rn N)) (θ : Rn N → ℝ) (μ : Measure (Rn N)), NullMeasurableSet M μHE[n] → IsPositiveLocallyIntegrableWeight n M θ → μ = ((μHE[n] : Measure (Rn N)).restrict M).withDensity (fun z ↦ ENNReal.ofReal (θ z)) → (∀ K : Set (Rn N), IsCompact K → μ K < ∞) ∧ (∀ S : Set (Rn N), μ S = 0 ↔ μHE[n] (M ∩ S) = 0) ∧ ∀ (x : Rn N) (P : Submodule ℝ (Rn N)), HasWeightedApproximateTangentSpaceAt n M θ x P → HasApproxTangentPlaneWithMultiplicity n μ x P (θ x)`

## Sibling prerequisites

- `root.tangent_characterizations-a1.blowup_change_of_variables-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
