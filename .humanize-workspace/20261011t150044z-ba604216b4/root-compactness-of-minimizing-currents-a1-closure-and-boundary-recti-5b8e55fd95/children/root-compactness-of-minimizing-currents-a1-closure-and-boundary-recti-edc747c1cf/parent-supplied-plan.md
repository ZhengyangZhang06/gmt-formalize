# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.local_filling-a1.small_scale-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-edc747c1cf/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.local_filling-a1`
- Child key: `small_scale`
- Declaration: `Submission.cbrldlf_exists_small_scale_of_lower_density`
- Exact Lean type: `∀ n : ℕ, 0 < (unitBallVolume n).toReal ∧ ∀ (P : ℕ) (μ : Measure (Euclid P)) (x₁ : Euclid P) (η₀ δ : ℝ), 0 < δ → liminf (fun r : ℝ => μ (ball x₁ r) / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0) < ENNReal.ofReal η₀ → ∃ s : ℝ, 0 < s ∧ s < δ ∧ μ (ball x₁ s) < ENNReal.ofReal (η₀ * (unitBallVolume n).toReal * s ^ n)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
