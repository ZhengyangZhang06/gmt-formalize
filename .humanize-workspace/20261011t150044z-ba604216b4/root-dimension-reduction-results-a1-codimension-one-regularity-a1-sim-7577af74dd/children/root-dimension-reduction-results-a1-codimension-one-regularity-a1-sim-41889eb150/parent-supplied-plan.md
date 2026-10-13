# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.subspace_ball_measure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-41889eb150/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1`
- Child key: `subspace_ball_measure`
- Declaration: `Submission.codim1_subspace_ball_euclideanHausdorff`
- Exact Lean type: `∀ (P m : ℕ) (H₀ : Submodule ℝ (Euclid P)), Module.finrank ℝ H₀ = m → ∀ ρ : ℝ, 0 < ρ → μHE[m] ((H₀ : Set (Euclid P)) ∩ ball 0 ρ) = unitBallVolume m * ENNReal.ofReal (ρ ^ m)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
