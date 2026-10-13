# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.mass_representation-a1.representation_core-a1.mass_lower_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-rep-1955ca3d37/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.representation_core-a1`
- Child key: `mass_lower_bound`
- Declaration: `Submission.cmrc_measure_le_massOn_of_norming`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n) (β : Euclid P → Covector (Euclid P) n), (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) → AEStronglyMeasurable β μ → (∃ C : ℝ, ∀ x, ‖β x‖ ≤ C) → (∀ x, covectorEuclideanNorm (β x) ≤ 1) → (∀ᵐ x ∂μ, ξ x (β x) = 1) → ∀ W W' : Set (Euclid P), IsOpen W' → CompactlyContained W' U → W' ⊆ W → μ W' ≤ T.massOn W`

## Sibling prerequisites

- `root.regular_set_dense-a1.mass_eq_weight-a1.test_form_approx-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
