# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.smooth_to_c1_tests-a1.mollify_deriv_approx-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-34615cc648/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.smooth_to_c1_tests-a1`
- Child key: `mollify_deriv_approx`
- Declaration: `Submission.dgcr_stc_mollify_C1_fderiv_approx`
- Exact Lean type: `∀ (n : ℕ) (φ : Euclid n → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ → ∀ (δ : ℝ), 0 < δ → ∀ (v : Euclid n) (ε : ℝ), 0 < ε → ∃ ψ : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ cthickening δ (tsupport φ) ∧ ∀ x, |fderiv ℝ ψ x v - fderiv ℝ φ x v| ≤ ε`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.smooth_to_c1_tests-a1.normalized_mollifier-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
