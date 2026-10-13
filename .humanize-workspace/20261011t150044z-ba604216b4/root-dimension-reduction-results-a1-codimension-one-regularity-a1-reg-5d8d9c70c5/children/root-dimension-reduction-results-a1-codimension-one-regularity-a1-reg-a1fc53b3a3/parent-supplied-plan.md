# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.pushforward_rep-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-a1fc53b3a3/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1`
- Child key: `pushforward_rep`
- Declaration: `Submission.codim1_lur_gauss_green_pushforward`
- Exact Lean type: `∀ (P n : ℕ) (x : Euclid P) (ι : Euclid (n + 1) →ₗᵢ[ℝ] Euclid P) (u : Euclid (n + 1) → Euclid P) (δ₁ δ₂ : ℝ) (B : Set (Euclid (n + 1))) (ν : Euclid (n + 1) → Euclid (n + 1)), 1 ≤ n → 0 < δ₁ → ContDiffOn ℝ 1 u (ball 0 δ₁) → (∀ v ∈ ball (0 : Euclid (n + 1)) δ₁, (∀ w : Euclid (n + 1), inner ℝ (ι w) (u v) = 0) ∧ ‖u v‖ < δ₂) → MeasurableSet B → B ⊆ ball 0 δ₁ → CountablyRectifiable n B → (∀ K : Set (Euclid (n + 1)), IsCompact K → K ⊆ ball 0 δ₁ → μHE[n] (B ∩ K) ≠ ∞) → Measurable ν → (∀ y ∈ B, ‖ν y‖ = 1) → (∀ᵐ y ∂(μHE[n].restrict B), HasApproximateTangentSpaceAt n B y (Submodule.span ℝ {ν y})ᗮ) → ∃ (M' : Set (Euclid P)) (ξ' : Euclid P → MultiVector P n), MeasurableSet M' ∧ M' ⊆ {w : Euclid P | ‖ContinuousLinearMap.adjoint ι.toContinuousLinearMap (w - x)‖ < δ₁ / 2 ∧ ‖w - x - ι (ContinuousLinearMap.adjoint ι.toContinuousLinearMap (w - x))‖ < δ₂} ∧ CountablyRectifiable n M' ∧ μHE[n] M' ≠ ∞ ∧ AEStronglyMeasurable ξ' (μHE[n].restrict M') ∧ (∀ᵐ w ∂(μHE[n].restrict M'), ∃ Q : Submodule ℝ (Euclid P), IsUnitOrientationOf (ξ' w) Q) ∧ ∀ ω : DifferentialForm (Euclid P) n, tsupport ω ⊆ {w : Euclid P | ‖ContinuousLinearMap.adjoint ι.toContinuousLinearMap (w - x)‖ < δ₁ / 2 ∧ ‖w - x - ι (ContinuousLinearMap.adjoint ι.toContinuousLinearMap (w - x))‖ < δ₂} → -∫ v in B, inner ℝ ((ball (0 : Euclid (n + 1)) δ₁).indicator (fun v => ∑ j : Fin (n + 1), ((-1 : ℝ) ^ (j : ℕ) * ω (x + ι v + u v) (fun k => fderiv ℝ (fun y => x + ι y + u y) v (EuclideanSpace.single (j.succAbove k) 1))) • EuclideanSpace.single j (1 : ℝ)) v) (ν v) ∂μHE[n] = ∫ w in M', ξ' w (ω w) ∂μHE[n]`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.area_formula-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.normal_orientation-a1`
- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.wedge_orientation-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
