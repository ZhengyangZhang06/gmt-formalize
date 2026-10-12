# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.indicator_compactness-a1.l1_duality-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-indicator-compactness-a1-l1-duality-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.indicator_compactness-a1`
- Child key: `l1_duality`
- Declaration: `Submission.indCompact_ball_integral_abs_le_of_test_bound`
- Exact Lean type: `∀ (N : ℕ) (w : Rn N → ℝ) (R M : ℝ), IntegrableOn w (Metric.ball (0 : Rn N) R) volume → (∀ ψ : Rn N → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ → tsupport ψ ⊆ Metric.ball (0 : Rn N) R → (∀ y, |ψ y| ≤ 1) → ∫ y, w y * ψ y ≤ M) → ∫ y in Metric.ball (0 : Rn N) R, |w y| ≤ M`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
