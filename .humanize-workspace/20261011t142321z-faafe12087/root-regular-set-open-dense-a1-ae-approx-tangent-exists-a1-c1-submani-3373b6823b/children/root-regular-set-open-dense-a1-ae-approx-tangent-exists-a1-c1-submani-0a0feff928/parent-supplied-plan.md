# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.c1_submanifold_tangent-a1.chart_lower_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-ae-approx-tangent-exists-a1-c1-submani-0a0feff928/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.c1_submanifold_tangent-a1`
- Child key: `chart_lower_bound`
- Declaration: `Submission.rsod_c1tan_chart_lower_bound`
- Exact Lean type: `∀ (m N : ℕ) (V : Set (Rn m)) (φ : Rn m → EuclideanSpace ℝ (Fin N)) (v₀ : Rn m), IsOpen V → ContDiffOn ℝ 1 φ V → v₀ ∈ V → Function.Injective (fderiv ℝ φ v₀) → ∃ c : ℝ, 0 < c ∧ ∃ δ : ℝ, 0 < δ ∧ closedBall v₀ δ ⊆ V ∧ ∀ w : Rn m, ‖w‖ ≤ δ → c * ‖w‖ ≤ ‖φ (v₀ + w) - φ v₀‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
