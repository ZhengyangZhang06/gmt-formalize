# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rectifiability-a1.mass_measure_rectifiable-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-mass-measure-rectifiable-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rectifiability-a1`
- Child key: `mass_measure_rectifiable`
- Declaration: `Submission.rectifiability_mass_measure_rectifiable`
- Exact Lean type: `∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : GeometricCurrentOn U (m + 1), (∀ W, CompactlyContainedOpen W U → T.massOn W + T.boundary.massOn W < ∞) → ∀ μ : Measure (Eucl P), IsMassMeasure T μ → (∀ᵐ x ∂μ, 0 < dimensionalUpperDensity μ.toOuterMeasure ((m + 1 : ℕ) : ℝ) univ x) → ∃ (M : Set (Eucl P)) (θ : Eucl P → ℝ), M ⊆ U ∧ MeasurableSet M ∧ CountablyRectifiable (m + 1) M ∧ Measurable θ ∧ (∀ x ∈ M, 0 < θ x) ∧ (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → IntegrableOn θ (M ∩ K) (μHE[m + 1] : Measure (Eucl P))) ∧ μ = ((μHE[m + 1] : Measure (Eucl P)).restrict M).withDensity (fun x => ENNReal.ofReal (θ x))`

## Sibling prerequisites

- `root.rectifiability-a1.projection_null-a1`
- `root.rectifiability-a1.mass_measure_abs_continuous-a1`
- `root.rectifiability-a1.density_comparison-a1`
- `root.rectifiability-a1.structure_projection-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
