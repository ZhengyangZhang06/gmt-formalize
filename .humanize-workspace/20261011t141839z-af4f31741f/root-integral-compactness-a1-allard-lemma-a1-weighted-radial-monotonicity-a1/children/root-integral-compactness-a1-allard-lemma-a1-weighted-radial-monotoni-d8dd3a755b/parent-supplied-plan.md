# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.allard_lemma-a1.weighted_radial_monotonicity-a1.cutoff_mass_derivative-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1-weighted-radial-monotoni-d8dd3a755b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.allard_lemma-a1.weighted_radial_monotonicity-a1`
- Child key: `cutoff_mass_derivative`
- Declaration: `Submission.intcpt_allard_wrm_cutoff_mass_hasDerivAt`
- Exact Lean type: `∀ (N : ℕ) (μ : Measure (Euclidean N)) (y : Euclidean N) (h : Euclidean N → ℝ) (φ : ℝ → ℝ) (A R t₀ : ℝ), Continuous h → ContDiff ℝ 1 φ → 0 < A → (∀ s, A ^ 2 ≤ s → φ s = 0) → μ (closedBall y R) ≠ ∞ → 0 < t₀ → t₀ * A < R → HasDerivAt (fun t : ℝ ↦ ∫ z, φ (‖z - y‖ ^ 2 / t ^ 2) * h z ∂μ) (∫ z, deriv φ (‖z - y‖ ^ 2 / t₀ ^ 2) * (-2 * ‖z - y‖ ^ 2 / t₀ ^ 3) * h z ∂μ) t₀`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
