# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.stationary_results-a1.sff_chart-a1.immersion_left_inverse-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1-sff-chart-a1-immersion-left-inverse-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.stationary_results-a1.sff_chart-a1`
- Child key: `immersion_left_inverse`
- Declaration: `Submission.sff_immersion_local_left_inverse`
- Exact Lean type: `∀ (n N : ℕ) (ψ : Rn n → Rn N) (x₀ : Rn n), ContDiffAt ℝ 1 ψ x₀ → Function.Injective (fderiv ℝ ψ x₀) → ∃ g : Rn N → Rn n, DifferentiableAt ℝ g (ψ x₀) ∧ ∀ᶠ x in 𝓝 x₀, g (ψ x) = x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
