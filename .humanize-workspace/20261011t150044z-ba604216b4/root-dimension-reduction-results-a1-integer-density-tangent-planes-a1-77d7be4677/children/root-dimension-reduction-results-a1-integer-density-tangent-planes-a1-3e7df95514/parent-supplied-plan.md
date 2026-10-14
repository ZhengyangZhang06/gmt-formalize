# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.planar_constancy-a1.plane_constancy_reduction-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-3e7df95514/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.planar_constancy-a1`
- Child key: `plane_constancy_reduction`
- Declaration: `Submission.idtp_pc_constancy_reduction`
- Exact Lean type: `∀ (P n : ℕ) (V : Set (Euclid P)) (τ : Fin n → Euclid P) (g : Euclid P → ℝ), IsOpen V → Orthonormal ℝ τ → IsConnected (V ∩ (Submodule.span ℝ (Set.range τ) : Set (Euclid P))) → AEStronglyMeasurable g (μHE[n].restrict (Submodule.span ℝ (Set.range τ) : Set (Euclid P))) → (∀ᵐ x ∂(μHE[n].restrict (Submodule.span ℝ (Set.range τ) : Set (Euclid P))), ∃ m : ℤ, g x = m) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ V → ∫⁻ x in K ∩ (Submodule.span ℝ (Set.range τ) : Set (Euclid P)), ‖g x‖ₑ ∂μHE[n] ≠ ∞) → (∀ f : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → tsupport f ⊆ V → ∀ j : Fin n, ∫ x in V ∩ (Submodule.span ℝ (Set.range τ) : Set (Euclid P)), g x * fderiv ℝ f x (τ j) ∂μHE[n] = 0) → IsOpen {s : Euclid n | ∑ i, s i • τ i ∈ V} ∧ IsPreconnected {s : Euclid n | ∑ i, s i • τ i ∈ V} ∧ LocallyIntegrableOn (fun s : Euclid n => g (∑ i, s i • τ i)) {s : Euclid n | ∑ i, s i • τ i ∈ V} volume ∧ (∀ φ : Euclid n → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ {s : Euclid n | ∑ i, s i • τ i ∈ V} → ∀ i : Fin n, ∫ s, g (∑ k, s k • τ k) * fderiv ℝ φ s ((EuclideanSpace.basisFun (Fin n) ℝ) i) = 0) ∧ ∀ c₀ : ℝ, (∀ᵐ s ∂(volume.restrict {s : Euclid n | ∑ i, s i • τ i ∈ V}), g (∑ i, s i • τ i) = c₀) → ∃ c : ℤ, ∀ᵐ x ∂(μHE[n].restrict (V ∩ (Submodule.span ℝ (Set.range τ) : Set (Euclid P)))), g x = c`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.planar_constancy-a1.plane_measure_map-a1`
- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.planar_constancy-a1.plane_test_extension-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.smooth_to_c1_tests-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
