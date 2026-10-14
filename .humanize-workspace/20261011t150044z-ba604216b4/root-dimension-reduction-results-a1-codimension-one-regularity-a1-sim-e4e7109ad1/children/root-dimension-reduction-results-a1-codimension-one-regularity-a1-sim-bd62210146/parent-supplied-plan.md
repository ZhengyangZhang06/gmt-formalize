# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1.graph_chart-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-bd62210146/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.smooth_regularity-a1`
- Child key: `graph_chart`
- Declaration: `Submission.codim1_hcp_sr_graph_chart`
- Exact Lean type: `∀ (P m : ℕ) (M : Set (Euclid P)) (y : Euclid P), 1 ≤ m → IsEmbeddedSubmanifold 1 m M → y ∈ M → ∃ (ι : Euclid m →ₗᵢ[ℝ] Euclid P) (ι' : Euclid (P - m) →ₗᵢ[ℝ] Euclid P), (∀ a b, inner ℝ (ι a) (ι' b) = 0) ∧ (∀ z : Euclid P, ∃ a b, z = ι a + ι' b) ∧ ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∃ (s t : ℝ) (u : Euclid m → Euclid (P - m)), 0 < s ∧ 0 < t ∧ s + t ≤ δ ∧ ContDiffOn ℝ 1 u (ball 0 s) ∧ u 0 = 0 ∧ (∀ a ∈ ball (0 : Euclid m) s, ‖fderiv ℝ u a‖ ≤ ε ∧ ‖u a‖ < t) ∧ IsOpen {z : Euclid P | ∃ a ∈ ball (0 : Euclid m) s, ∃ b ∈ ball (0 : Euclid (P - m)) t, z = y + ι a + ι' b} ∧ M ∩ {z : Euclid P | ∃ a ∈ ball (0 : Euclid m) s, ∃ b ∈ ball (0 : Euclid (P - m)) t, z = y + ι a + ι' b} = (fun a => y + ι a + ι' (u a)) '' ball 0 s ∧ InjOn (fun a => y + ι a + ι' (u a)) (ball 0 s) ∧ (∀ a ∈ ball (0 : Euclid m) s, Injective (fderiv ℝ (fun a => y + ι a + ι' (u a)) a) ∧ tangentSpace M (y + ι a + ι' (u a)) = Set.range (fderiv ℝ (fun a => y + ι a + ι' (u a)) a)) ∧ ∀ K ⊆ {z : Euclid P | ∃ a ∈ ball (0 : Euclid m) s, ∃ b ∈ ball (0 : Euclid (P - m)) t, z = y + ι a + ι' b}, IsCompact K → IsCompact (ball (0 : Euclid m) s ∩ (fun a => y + ι a + ι' (u a)) ⁻¹' K)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
