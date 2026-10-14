# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1.harmonic_decay-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-48fb867a19/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1`
- Child key: `harmonic_decay`
- Declaration: `Submission.codim1_hcp_sr_harmonic_decay`
- Exact Lean type: `∀ (m k : ℕ), 1 ≤ m → ∃ C : ℝ, 0 < C ∧ ∀ (x₀ : Euclid m) (R : ℝ) (h : Euclid m → Euclid k), 0 < R → (∀ n : ℕ, ContDiffOn ℝ n h (ball x₀ R)) → (∀ x ∈ ball x₀ R, ∑ i : Fin m, iteratedFDeriv ℝ 2 h x ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0) → IntegrableOn (fun x => ∑ j : Fin m, ‖fderiv ℝ h x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) (ball x₀ R) → ∀ r : ℝ, 0 < r → r ≤ R → (∫ x in ball x₀ r, ∑ j : Fin m, ‖(fderiv ℝ h x - ⨍ z in ball x₀ r, fderiv ℝ h z) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤ C * (r / R) ^ (m + 2) * ∫ x in ball x₀ R, ∑ j : Fin m, ‖(fderiv ℝ h x - ⨍ z in ball x₀ R, fderiv ℝ h z) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) ∧ ∫ x in ball x₀ r, ∑ j : Fin m, ‖fderiv ℝ h x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤ C * (r / R) ^ m * ∫ x in ball x₀ R, ∑ j : Fin m, ‖fderiv ℝ h x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.interior_estimates-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
