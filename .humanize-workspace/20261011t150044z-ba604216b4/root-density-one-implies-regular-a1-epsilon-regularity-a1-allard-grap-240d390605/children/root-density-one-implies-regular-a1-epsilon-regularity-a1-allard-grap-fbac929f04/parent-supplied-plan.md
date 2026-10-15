# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.monotonicity-a1.radial_variation-a1.radial_field_c1-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-fbac929f04/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.monotonicity-a1.radial_variation-a1`
- Child key: `radial_field_c1`
- Declaration: `Submission.doragm_rfv_radial_field_c1`
- Exact Lean type: `∀ (P : ℕ) (y : Euclid P) (φ : ℝ → ℝ) (A τ : ℝ), ContDiff ℝ 1 φ → (∀ u, u ≤ 1 → φ u = 1) → (∀ u, A ≤ u → φ u = 0) → 0 < τ → ContDiff ℝ 1 (fun x : Euclid P => φ (‖x - y‖ / τ) • (x - y)) ∧ HasCompactSupport (fun x : Euclid P => φ (‖x - y‖ / τ) • (x - y)) ∧ tsupport (fun x : Euclid P => φ (‖x - y‖ / τ) • (x - y)) ⊆ closedBall y (A * τ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
