# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rectifiability-a1.mass_measure_rectifiable-a1.positive_density_cover_null-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-mass-measure-rectifiable-a1-positive-density-c-4b4a9741fc/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rectifiability-a1.mass_measure_rectifiable-a1`
- Child key: `positive_density_cover_null`
- Declaration: `Submission.rectifiability_positive_density_cover_null`
- Exact Lean type: `∀ (P n : ℕ) (ν : Measure (Eucl P)) (W : ℕ → Set (Eucl P)) (S : Set (Eucl P)), (∀ q, IsOpen (W q)) → (∀ q, ν (W q) < ∞) → S ⊆ ⋃ q, W q → (∀ x ∈ S, 0 < dimensionalUpperDensity ν.toOuterMeasure (n : ℝ) univ x) → (∃ C : ℕ → Set (Eucl P), S ⊆ ⋃ i, C i ∧ ∀ i, (μHE[n] : Measure (Eucl P)) (C i) < ∞) ∧ (ν S = 0 → (μHE[n] : Measure (Eucl P)) S = 0)`

## Sibling prerequisites

- `root.rectifiability-a1.density_comparison-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
