# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.bv_compactness-a1.smooth_variation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-e87340558c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.bv_compactness-a1`
- Child key: `smooth_variation`
- Declaration: `Submission.codim1_zsl_pc_smooth_grad_bound`
- Exact Lean type: `∀ (m : ℕ) (g : Euclid m → ℝ) (r c : ℝ), ContDiff ℝ (⊤ : ℕ∞) g → (∀ ψ : Euclid m → Euclid m, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ ball (0 : Euclid m) r → (∀ v, ‖ψ v‖ ≤ 1) → ∫ v, g v * LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ v).toLinearMap ≤ c) → ∫⁻ v in ball (0 : Euclid m) r, ‖fderiv ℝ g v‖ₑ ≤ ENNReal.ofReal c`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.energy_lsc-a1.ibp_c1_ball-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
