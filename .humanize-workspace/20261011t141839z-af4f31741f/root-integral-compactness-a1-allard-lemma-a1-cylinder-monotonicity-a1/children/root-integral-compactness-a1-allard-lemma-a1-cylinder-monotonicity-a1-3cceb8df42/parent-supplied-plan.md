# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.allard_lemma-a1.cylinder_monotonicity-a1.cutoff_integral_tendsto-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1-cylinder-monotonicity-a1-3cceb8df42/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.allard_lemma-a1.cylinder_monotonicity-a1`
- Child key: `cutoff_integral_tendsto`
- Declaration: `Submission.intcpt_allard_cm_cutoff_integral_tendsto`
- Exact Lean type: `∀ (N : ℕ) (μ : Measure (Euclidean N)) (y : Euclidean N) (h : Euclidean N → ℝ) (φ : ℕ → ℝ → ℝ) (A : ℕ → ℝ) (t R : ℝ), Measurable h → (∀ z, 0 ≤ h z ∧ h z ≤ 1) → (∀ j, Measurable (φ j)) → (∀ j s, 0 ≤ φ j s ∧ φ j s ≤ 1) → (∀ j s, s ≤ 1 → φ j s = 1) → (∀ j s, A j ^ 2 ≤ s → φ j s = 0) → (∀ j, 0 < A j) → Tendsto A atTop (𝓝 1) → 0 < t → (∀ j, t * A j ≤ R) → μ (closedBall y R) ≠ ∞ → Tendsto (fun j ↦ ∫ z, φ j (‖z - y‖ ^ 2 / t ^ 2) * h z ∂μ) atTop (𝓝 (∫ z in closedBall y t, h z ∂μ))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
