# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.null_set-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-3d838668ea/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1`
- Child key: `null_set`
- Declaration: `Submission.cbrld_measure_eq_zero_of_small_fillings`
- Exact Lean type: `(∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → ∀ (P d : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (d + 1)) (κ lam : ℝ) (E : Set (Euclid P)), 0 ≤ κ → κ < 1 → 1 ≤ lam → (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → (∀ W : Set (Euclid P), IsOpen W → C.massOn W = μ W) → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (d + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), C ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ x ∈ E, ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧ μ (sphere x ρ) = 0 ∧ ∃ (A S : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)), (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), A ω = ∫ y in ball x ρ, ξ y ((ω : DifferentialForm (Euclid P) (d + 1)) y) ∂μ) ∧ S.boundary = A.boundary ∧ S.mass ≤ ENNReal.ofReal κ * μ (ball x ρ) ∧ S.support ⊆ closedBall x (lam * δ)) → μ E = 0`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.cone-a1`
- `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.covering-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
