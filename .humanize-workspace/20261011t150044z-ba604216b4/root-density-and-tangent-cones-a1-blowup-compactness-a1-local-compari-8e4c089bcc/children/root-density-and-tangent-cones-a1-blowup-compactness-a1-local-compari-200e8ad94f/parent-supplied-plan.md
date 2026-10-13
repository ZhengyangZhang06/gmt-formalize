# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.boundary_im-a1.de_giorgi-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-200e8ad94f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.flat_decomposition-a1.boundary_im-a1`
- Child key: `de_giorgi`
- Declaration: `Submission.dtc_bc_lc_fd_bim_de_giorgi`
- Exact Lean type: `∀ (n : ℕ) (E : Set (Euclid (n + 1))) (C : ℝ), 1 ≤ n → MeasurableSet E → (∀ φ : Euclid (n + 1) → Euclid (n + 1), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → (∀ y, ‖φ y‖ ≤ 1) → ∫ y in E, LinearMap.trace ℝ (Euclid (n + 1)) (fderiv ℝ φ y : Euclid (n + 1) →ₗ[ℝ] Euclid (n + 1)) ≤ C) → ∃ (B : Set (Euclid (n + 1))) (ν : Euclid (n + 1) → Euclid (n + 1)), MeasurableSet B ∧ CountablyRectifiable n B ∧ μHE[n] B ≠ ∞ ∧ Measurable ν ∧ (∀ y ∈ B, ‖ν y‖ = 1) ∧ (∀ᵐ y ∂(μHE[n].restrict B), HasApproximateTangentSpaceAt n B y (Submodule.span ℝ {ν y})ᗮ) ∧ (∀ φ : Euclid (n + 1) → Euclid (n + 1), ContDiff ℝ 1 φ → HasCompactSupport φ → ∫ y in E, LinearMap.trace ℝ (Euclid (n + 1)) (fderiv ℝ φ y : Euclid (n + 1) →ₗ[ℝ] Euclid (n + 1)) = -∫ y in B, inner ℝ (φ y) (ν y) ∂μHE[n]) ∧ ∀ᵐ y ∂(μHE[n].restrict B), ∀ ρ : ℝ, Tendsto (fun r : ℝ => volume (symmDiff ((fun w => y + r • w) ⁻¹' E) {w | 0 < inner ℝ w (ν y)} ∩ ball (0 : Euclid (n + 1)) ρ)) (𝓝[>] 0) (𝓝 0)`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.gauss_green_measure-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.hausdorff_identification-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.rectifiable_density_one-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
