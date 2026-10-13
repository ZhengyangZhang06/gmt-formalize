# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.allard_lemma-a1.cylinder_monotonicity-a1.cylinder_mass_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1-cylinder-monotonicity-a1-6e281d5d44/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.allard_lemma-a1.cylinder_monotonicity-a1`
- Child key: `cylinder_mass_bound`
- Declaration: `Submission.intcpt_allard_cm_cylinder_mass_bound`
- Exact Lean type: `∀ (N n : ℕ) (μ : Measure (Euclidean N)) (P : Grassmannian N n) (y : Euclidean N) (h : Euclidean N → ℝ) (τ σ ρ E : ℝ), Measurable h → (∀ z, 0 ≤ h z ∧ h z ≤ 1) → (∀ z, ‖(z - y) - Grassmannian.project P (z - y)‖ < τ → h z = 1) → (∀ z, 2 * τ ≤ ‖(z - y) - Grassmannian.project P (z - y)‖ → h z = 0) → 0 < σ → σ ≤ ρ → μ (closedBall y ρ) ≠ ∞ → (∫ z in closedBall y σ, h z ∂μ) / σ ^ n ≤ (∫ z in closedBall y ρ, h z ∂μ) / ρ ^ n + E → μ (closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ}) / ENNReal.ofReal σ ^ n ≤ μ (closedBall y ρ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 2 * τ}) / ENNReal.ofReal ρ ^ n + ENNReal.ofReal E`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
