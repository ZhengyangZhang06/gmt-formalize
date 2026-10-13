# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_area-a1.relative_lipschitz-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-668e670990/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_area-a1`
- Child key: `relative_lipschitz`
- Declaration: `Submission.codim1_zsl_ga_relative_lipschitz_measure`
- Exact Lean type: `∀ (n P : ℕ) (F L : Euclid n → Euclid P) (S : Set (Euclid n)) (a b : ℝ), 0 < a → 0 ≤ b → (∀ x ∈ S, ∀ y ∈ S, a * ‖L x - L y‖ ≤ ‖F x - F y‖ ∧ ‖F x - F y‖ ≤ b * ‖L x - L y‖) → ENNReal.ofReal (a ^ n) * μHE[n] (L '' S) ≤ μHE[n] (F '' S) ∧ μHE[n] (F '' S) ≤ ENNReal.ofReal (b ^ n) * μHE[n] (L '' S)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
