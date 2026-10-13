# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.boundary_full_measure-a1.open_ball_differentiation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-boundary-full-measure-a1-open-ball-differentiation-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.boundary_full_measure-a1`
- Child key: `open_ball_differentiation`
- Declaration: `Submission.deGiorgiBFM_normalAverage_tendsto_ae`
- Exact Lean type: `∀ (N : ℕ) (μ : Measure (Rn N)) (f : Rn N → Rn N), IsFiniteMeasure μ → Integrable f μ → ∀ᵐ x ∂μ, Tendsto (normalAverage μ f x) (𝓝[>] 0) (𝓝 (f x))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
