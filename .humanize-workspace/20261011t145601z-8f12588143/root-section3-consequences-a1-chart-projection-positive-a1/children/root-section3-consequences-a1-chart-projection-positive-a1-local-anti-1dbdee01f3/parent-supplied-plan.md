# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.section3_consequences-a1.chart_projection_positive-a1.local_antilipschitz-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-section3-consequences-a1-chart-projection-positive-a1-local-anti-1dbdee01f3/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.section3_consequences-a1.chart_projection_positive-a1`
- Child key: `local_antilipschitz`
- Declaration: `Submission.section3_hasStrictFDerivAt_injective_local_antilipschitz`
- Exact Lean type: `∀ (n p : ℕ) (Φ : Rn n → Rn p) (A : Rn n →L[ℝ] Rn p) (u₀ : Rn n), HasStrictFDerivAt Φ A u₀ → Function.Injective A → ∃ s ∈ 𝓝 u₀, ∃ K : ℝ≥0, ∀ x ∈ s, ∀ y ∈ s, ‖x - y‖ ≤ K * ‖Φ x - Φ y‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
