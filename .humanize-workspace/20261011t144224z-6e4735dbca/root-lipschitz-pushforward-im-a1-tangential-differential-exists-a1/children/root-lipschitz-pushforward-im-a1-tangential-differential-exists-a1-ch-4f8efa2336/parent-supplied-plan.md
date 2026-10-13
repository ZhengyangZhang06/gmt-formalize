# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_pushforward_im-a1.tangential_differential_exists-a1.chart_directional_deriv-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1-ch-4f8efa2336/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_pushforward_im-a1.tangential_differential_exists-a1`
- Child key: `chart_directional_deriv`
- Declaration: `Submission.lpf_tde_chart_directional_deriv`
- Exact Lean type: `∀ (P Q n : ℕ) (f : Eucl P → Eucl Q) (Φ : Eucl n → Eucl P) (w : Eucl n) (A : Eucl n →L[ℝ] Eucl P) (B : Eucl n →L[ℝ] Eucl Q) (K : ℝ≥0) (ρ : ℝ), 0 < ρ → LipschitzOnWith K f (ball (Φ w) ρ) → HasFDerivAt Φ A w → HasFDerivAt (f ∘ Φ) B w → ∀ s : Eucl n, HasDerivAt (fun t : ℝ => f (Φ w + t • A s)) (B s) 0 ∧ ‖B s‖ ≤ (K : ℝ) * ‖A s‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
