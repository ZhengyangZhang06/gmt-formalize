# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rectifiability-a1.orientation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-orientation-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rectifiability-a1`
- Child key: `orientation`
- Declaration: `Submission.rectifiability_orientation`
- Exact Lean type: `∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : GeometricCurrentOn U (m + 1), (∀ W, CompactlyContainedOpen W U → T.boundary.massOn W < ∞) → ∀ (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) (m + 1)), M ⊆ U → NullMeasurableSet M (μHE[m + 1] : Measure (Eucl P)) → CountablyRectifiable (m + 1) M → (∀ x ∈ M, 0 < θ x) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → IntegrableOn θ (M ∩ K) (μHE[m + 1] : Measure (Eucl P))) → AEStronglyMeasurable ξ ((μHE[m + 1] : Measure (Eucl P)).restrict M) → (∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), ∑ α : SimonMultiIndex (m + 1) P, (euclideanNVectorCoordinate (ξ x) α) ^ 2 = 1) → (∀ ω : TestFormOn U (m + 1), T ω = tauAction (m + 1) M θ ξ ω) → ∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), ∃ τ : Fin (m + 1) → Eucl P, Orthonormal ℝ τ ∧ HasWeightedApproximateTangentSpaceAt (m + 1) M θ x (Submodule.span ℝ (range τ)) ∧ (ξ x = simpleNVector τ ∨ ξ x = -simpleNVector τ)`

## Sibling prerequisites

- `root.rectifiability-a1.mass_measure_representation-a1`
- `root.rectifiability-a1.density_comparison-a1`
- `root.rectifiability-a1.weighted_tangent_ae-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
