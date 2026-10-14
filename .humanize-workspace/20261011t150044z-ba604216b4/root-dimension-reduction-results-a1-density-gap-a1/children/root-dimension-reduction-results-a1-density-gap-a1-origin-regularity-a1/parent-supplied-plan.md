# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.density_gap-a1.origin_regularity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-density-gap-a1-origin-regularity-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.density_gap-a1`
- Child key: `origin_regularity`
- Declaration: `Submission.dimred_cdg_minimizing_origin_regular`
- Exact Lean type: `∀ (P j : ℕ), 1 ≤ j → j ≤ P → ∃ δ : ℝ, 0 < δ ∧ ∀ C : GeometricCurrentOn (univ : Set (Euclid P)) j, IsMinimizingIn C univ → BoundaryVanishes C → (0 : Euclid P) ∈ C.support → (∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → C.massOn (ball 0 ρ) ≤ ENNReal.ofReal (1 + δ) * unitBallVolume j * ENNReal.ofReal (ρ ^ j)) → (0 : Euclid P) ∈ regularSet C`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1`
- `root.dimension_reduction_results-a1.density_gap-a1.c1_pushforward-a1`
- `root.dimension_reduction_results-a1.density_gap-a1.first_variation_bound-a1`
- `root.dimension_reduction_results-a1.density_gap-a1.allard_graph-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
