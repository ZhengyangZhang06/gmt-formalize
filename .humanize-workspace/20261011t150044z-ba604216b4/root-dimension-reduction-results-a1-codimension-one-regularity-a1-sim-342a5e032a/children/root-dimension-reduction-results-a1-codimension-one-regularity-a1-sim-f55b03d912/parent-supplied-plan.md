# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.unit_normal-a1.chart_retraction-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-f55b03d912/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.unit_normal-a1`
- Child key: `chart_retraction`
- Declaration: `Submission.codim1_hcp_un_chart_retraction`
- Exact Lean type: `∀ (P d : ℕ) (M W : Set (Euclid P)) (V : Set (Euclid d)) (ψ : Euclid d → Euclid P) (v₀ : Euclid d), IsOpen V → IsOpen W → ContDiffOn ℝ (⊤ : ℕ∞) ψ V → InjOn ψ V → ψ '' V = W ∩ M → (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) → (∀ z ∈ V, Injective (fderiv ℝ ψ z)) → v₀ ∈ V → ∃ (O : Set (Euclid P)) (ρ : Euclid P → Euclid d), IsOpen O ∧ ψ v₀ ∈ O ∧ ContDiffOn ℝ (⊤ : ℕ∞) ρ O ∧ MapsTo ρ O V ∧ ∀ z ∈ M ∩ O, ψ (ρ z) = z`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
