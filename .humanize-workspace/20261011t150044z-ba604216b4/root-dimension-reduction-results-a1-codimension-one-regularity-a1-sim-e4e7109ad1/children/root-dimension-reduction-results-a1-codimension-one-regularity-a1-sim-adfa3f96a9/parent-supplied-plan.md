# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1.harmonic_replacement-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-adfa3f96a9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1`
- Child key: `harmonic_replacement`
- Declaration: `Submission.codim1_hcp_sr_harmonic_replacement`
- Exact Lean type: `∀ (m k : ℕ), 1 ≤ m → ∀ (x₀ : Euclid m) (R R' : ℝ) (w : Euclid m → Euclid k) (F : Euclid m → (Euclid m →L[ℝ] Euclid k)), 0 < R → R < R' → ContDiffOn ℝ 1 w (ball x₀ R') → ContinuousOn F (ball x₀ R') → (∀ ζ : Euclid m → Euclid k, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball x₀ R → ∫ x in ball x₀ R, ∑ j : Fin m, inner ℝ (fderiv ℝ w x (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ))) = ∫ x in ball x₀ R, ∑ j : Fin m, inner ℝ (F x (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ)))) → ∃ h : Euclid m → Euclid k, (∀ n : ℕ, ContDiffOn ℝ n h (ball x₀ R)) ∧ (∀ x ∈ ball x₀ R, ∑ i : Fin m, iteratedFDeriv ℝ 2 h x ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0) ∧ IntegrableOn (fun x => ∑ j : Fin m, ‖(fderiv ℝ w x - fderiv ℝ h x) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) (ball x₀ R) ∧ ∀ c : Euclid m →L[ℝ] Euclid k, ∫ x in ball x₀ R, ∑ j : Fin m, ‖(fderiv ℝ w x - fderiv ℝ h x) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤ ∫ x in ball x₀ R, ∑ j : Fin m, ‖(F x - c) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.weyl_lemma-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
