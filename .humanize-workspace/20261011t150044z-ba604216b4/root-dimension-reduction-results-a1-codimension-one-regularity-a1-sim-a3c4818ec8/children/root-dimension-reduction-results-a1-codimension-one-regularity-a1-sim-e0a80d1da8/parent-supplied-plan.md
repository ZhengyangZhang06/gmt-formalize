# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.simons_cone-a1.stationary_ibp-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-e0a80d1da8/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.simons_cone-a1`
- Child key: `stationary_ibp`
- Declaration: `Submission.codim1_hcp_sc_stationary_integration_by_parts`
- Exact Lean type: `∀ (P m : ℕ) (A₀ : Submodule ℝ (Euclid P)) (M : Set (Euclid P)) (ν : Euclid P → Euclid P), Module.finrank ℝ A₀ = m + 1 → M ⊆ (A₀ : Set (Euclid P)) → (0 : Euclid P) ∉ M → IsEmbeddedSubmanifold 1 m M → MeasurableSet M → (∀ K : Set (Euclid P), IsCompact K → μHE[m] (M ∩ K) ≠ ∞) → (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → (0 : Euclid P) ∉ tsupport X → ∫ x in M, LinearMap.trace ℝ (Euclid P) ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ (fderiv ℝ X x).toLinearMap) ∂μHE[m] = 0) → (∃ O : Set (Euclid P), IsOpen O ∧ M ⊆ O ∧ ContDiffOn ℝ (⊤ : ℕ∞) ν O) → (∀ x ∈ M, ν x ∈ A₀ ∧ ‖ν x‖ = 1 ∧ ∀ v ∈ tangentSpace M x, inner ℝ (ν x) v = 0) → ((∀ (ζ : Euclid P → ℝ), LocallyLipschitzOn M ζ → ∀ j : Fin P, AEStronglyMeasurable (fun x => fderivWithin ℝ ζ M x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))) (μHE[m].restrict M)) ∧ ∀ (ζ : Euclid P → ℝ), LocallyLipschitzOn M ζ → (∃ C : Set (Euclid P), IsCompact C ∧ C ⊆ M ∧ ∀ x ∈ M, x ∉ C → ζ x = 0) → ∃ (C' : Set (Euclid P)) (ζs : ℕ → Euclid P → ℝ), IsCompact C' ∧ C' ⊆ M ∧ (∀ k, ContDiff ℝ (⊤ : ℕ∞) (ζs k) ∧ HasCompactSupport (ζs k)) ∧ (∀ k, ∀ x ∈ M, x ∉ C' → ζs k x = 0) ∧ TendstoUniformlyOn ζs ζ atTop M ∧ Tendsto (fun k => ∫⁻ x in M, ENNReal.ofReal (∑ j : Fin P, (fderiv ℝ (ζs k) x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1)) - fderivWithin ℝ ζ M x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))) ^ 2) ∂μHE[m]) atTop (𝓝 0)) → ∀ (f F : Euclid P → ℝ) (O' : Set (Euclid P)), IsOpen O' → M ⊆ O' → ContDiffOn ℝ 2 F O' → (∀ y ∈ M, F y = f y) → ∀ φ : Euclid P → ℝ, LocallyLipschitzOn M φ → (∃ C : Set (Euclid P), IsCompact C ∧ C ⊆ M ∧ ∀ x ∈ M, x ∉ C → φ x = 0) → Integrable (fun x => ∑ j : Fin P, fderivWithin ℝ φ M x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1)) * fderivWithin ℝ f M x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))) (μHE[m].restrict M) ∧ Integrable (fun x => φ x * ∑ j : Fin P, fderivWithin ℝ (fun y => fderivWithin ℝ f M y ((Submodule.span ℝ (tangentSpace M y)).starProjection (EuclideanSpace.single j 1))) M x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))) (μHE[m].restrict M) ∧ ∫ x in M, (∑ j : Fin P, fderivWithin ℝ φ M x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1)) * fderivWithin ℝ f M x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))) ∂μHE[m] = -(∫ x in M, φ x * (∑ j : Fin P, fderivWithin ℝ (fun y => fderivWithin ℝ f M y ((Submodule.span ℝ (tangentSpace M y)).starProjection (EuclideanSpace.single j 1))) M x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))) ∂μHE[m])`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.simons_cone-a1.tangent_fderiv-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.simons_cone-a1.normal_complement-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
