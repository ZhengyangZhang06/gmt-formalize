# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1.stationary_mss-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-019464a990/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1`
- Child key: `stationary_mss`
- Declaration: `Submission.codim1_hcp_sr_stationary_mss`
- Exact Lean type: `∀ (m k : ℕ), 1 ≤ m → ∃ G : (Euclid m →L[ℝ] Euclid k) → (Euclid m →L[ℝ] Euclid k), ContDiff ℝ (⊤ : ℕ∞) G ∧ G 0 = 0 ∧ fderiv ℝ G 0 = 0 ∧ ∀ (P : ℕ) (U M : Set (Euclid P)) (y : Euclid P) (ι : Euclid m →ₗᵢ[ℝ] Euclid P) (ι' : Euclid k →ₗᵢ[ℝ] Euclid P) (s t : ℝ) (u : Euclid m → Euclid k), (∀ a b, inner ℝ (ι a) (ι' b) = 0) → (∀ z : Euclid P, ∃ a b, z = ι a + ι' b) → 0 < s → 0 < t → IsOpen U → {z : Euclid P | ∃ a ∈ ball (0 : Euclid m) s, ∃ b ∈ ball (0 : Euclid (k)) t, z = y + ι a + ι' b} ⊆ U → ContDiffOn ℝ 1 u (ball 0 s) → (∀ a ∈ ball (0 : Euclid m) s, ‖u a‖ < t) → M ∩ {z : Euclid P | ∃ a ∈ ball (0 : Euclid m) s, ∃ b ∈ ball (0 : Euclid (k)) t, z = y + ι a + ι' b} = (fun a => y + ι a + ι' (u a)) '' ball 0 s → (∀ a ∈ ball (0 : Euclid m) s, tangentSpace M (y + ι a + ι' (u a)) = Set.range (fderiv ℝ (fun a => y + ι a + ι' (u a)) a)) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[m] (M ∩ K) ≠ ∞) → (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U → ∫ x in M, LinearMap.trace ℝ (Euclid P) ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ (fderiv ℝ X x).toLinearMap) ∂μHE[m] = 0) → (∀ ζ : Euclid m → Euclid k, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Euclid m) s → ∫ x in ball (0 : Euclid m) s, ∑ j : Fin m, inner ℝ (fderiv ℝ u x (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ))) = ∫ x in ball (0 : Euclid m) s, ∑ j : Fin m, inner ℝ (G (fderiv ℝ u x) (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ))))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
