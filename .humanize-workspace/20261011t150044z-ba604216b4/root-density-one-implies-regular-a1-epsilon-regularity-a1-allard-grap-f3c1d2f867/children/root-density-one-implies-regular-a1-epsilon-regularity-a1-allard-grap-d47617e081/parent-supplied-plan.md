# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.monotonicity-a1.smoothed_bounds-a1.mass_sandwich-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-d47617e081/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.monotonicity-a1.smoothed_bounds-a1`
- Child key: `mass_sandwich`
- Declaration: `Submission.doragm_sab_cutoff_mass_sandwich`
- Exact Lean type: `∀ (P : ℕ) (μ : Measure (Euclid P)) (y : Euclid P) (φ : ℝ → ℝ) (A τ : ℝ), 0 < τ → (∀ u, 0 ≤ φ u ∧ φ u ≤ 1) → (∀ u, u ≤ 1 → φ u = 1) → (∀ u, A ≤ u → φ u = 0) → Integrable (fun x => φ (‖x - y‖ / τ)) μ → μ (closedBall y τ) ≤ ENNReal.ofReal (∫ x, φ (‖x - y‖ / τ) ∂μ) ∧ ENNReal.ofReal (∫ x, φ (‖x - y‖ / τ) ∂μ) ≤ μ (closedBall y (A * τ))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
