# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1.submanifold_approx_tangent-a1.c1_local_extension-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-9170e6c94d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.area_comparison-a1.submanifold_approx_tangent-a1`
- Child key: `c1_local_extension`
- Declaration: `Submission.codim1_ac_sat_c1_local_extension`
- Exact Lean type: `∀ (P m : ℕ) (V : Set (Euclid m)) (ψ : Euclid m → Euclid P) (v₀ : Euclid m), IsOpen V → ContDiffOn ℝ 1 ψ V → v₀ ∈ V → ∃ (g : Euclid m → Euclid P) (ρ : ℝ), 0 < ρ ∧ ball v₀ ρ ⊆ V ∧ ContDiff ℝ 1 g ∧ EqOn g ψ (ball v₀ ρ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
