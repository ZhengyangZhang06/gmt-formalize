# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_pushforward_im-a1.tangential_differential_exists-a1.chart_nondiff_image_null-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1-ch-34870e43f7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_pushforward_im-a1.tangential_differential_exists-a1`
- Child key: `chart_nondiff_image_null`
- Declaration: `Submission.lpf_tde_chart_nondiff_image_null`
- Exact Lean type: `∀ (P Q n : ℕ) (U : Set (Eucl P)) (f : Eucl P → Eucl Q) (Φ : Eucl n → Eucl P) (Ω : Set (Eucl n)) (K : ℝ≥0), IsOpen U → LocallyLipschitzOn U f → IsOpen Ω → LipschitzOnWith K Φ Ω → (μHE[n] : Measure (Eucl P)) (Φ '' {w | w ∈ Ω ∧ Φ w ∈ U ∧ ¬ DifferentiableAt ℝ (f ∘ Φ) w}) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
