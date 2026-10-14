# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.chart_divergence-a1.chart_geometry-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-f3cde17116/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.local_unit_rep-a1.chart_divergence-a1`
- Child key: `chart_geometry`
- Declaration: `Submission.codim1_lur_cd_graph_chart_geometry`
- Exact Lean type: `∀ (P n : ℕ) (N : Set (Euclid P)) (x : Euclid P) (ι : Euclid (n + 1) →ₗᵢ[ℝ] Euclid P) (u : Euclid (n + 1) → Euclid P) (δ₁ δ₂ : ℝ), ContDiffOn ℝ 2 u (ball 0 δ₁) → (∀ v ∈ ball (0 : Euclid (n + 1)) δ₁, ∀ w : Euclid (n + 1), inner ℝ (ι w) (u v) = 0) → (∀ v ∈ ball (0 : Euclid (n + 1)) δ₁, ‖u v‖ < δ₂ / 2) → (∀ v ∈ ball (0 : Euclid (n + 1)) δ₁, x + ι v + u v ∈ N) → (∀ (v : Euclid (n + 1)) (h : Euclid P), ‖v‖ < δ₁ → ‖h‖ < δ₂ → (∀ w : Euclid (n + 1), inner ℝ (ι w) h = 0) → x + ι v + h ∈ N → h = u v) → ContDiffOn ℝ 2 (fun y => x + ι y + u y) (ball 0 δ₁) ∧ (∀ v ∈ ball (0 : Euclid (n + 1)) δ₁, ∀ a : Euclid (n + 1), fderiv ℝ (fun y => x + ι y + u y) v a = ι a + fderiv ℝ u v a) ∧ (∀ v ∈ ball (0 : Euclid (n + 1)) δ₁, Function.Injective (fderiv ℝ (fun y => x + ι y + u y) v)) ∧ InjOn (fun y => x + ι y + u y) (ball 0 δ₁) ∧ IsOpen {w : Euclid P | ‖ContinuousLinearMap.adjoint ι.toContinuousLinearMap (w - x)‖ < δ₁ ∧ ‖w - x - ι (ContinuousLinearMap.adjoint ι.toContinuousLinearMap (w - x))‖ < δ₂} ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ {w : Euclid P | ‖ContinuousLinearMap.adjoint ι.toContinuousLinearMap (w - x)‖ < δ₁ ∧ ‖w - x - ι (ContinuousLinearMap.adjoint ι.toContinuousLinearMap (w - x))‖ < δ₂} → IsCompact (ball 0 δ₁ ∩ (fun y => x + ι y + u y) ⁻¹' K)) ∧ (∀ S : Set (Euclid P), S ⊆ N → S ∩ {w : Euclid P | ‖ContinuousLinearMap.adjoint ι.toContinuousLinearMap (w - x)‖ < δ₁ ∧ ‖w - x - ι (ContinuousLinearMap.adjoint ι.toContinuousLinearMap (w - x))‖ < δ₂} = (fun y => x + ι y + u y) '' (ball 0 δ₁ ∩ (fun y => x + ι y + u y) ⁻¹' S)) ∧ ∀ S : Set (Euclid P), MeasurableSet S → MeasurableSet (ball 0 δ₁ ∩ (fun y => x + ι y + u y) ⁻¹' S)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
