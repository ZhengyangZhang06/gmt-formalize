# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.allard_lemma-a1.weighted_radial_monotonicity-a1.gradient_term_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1-weighted-radial-monotoni-1ff4bad91c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.allard_lemma-a1.weighted_radial_monotonicity-a1`
- Child key: `gradient_term_bound`
- Declaration: `Submission.intcpt_allard_wrm_gradient_term_bound`
- Exact Lean type: `∀ (N n : ℕ) (U : Set (Euclidean N)) (W : Varifold N n U) (P : Grassmannian N n) (y : Euclidean N) (ε M A t : ℝ) (h : Euclidean N → ℝ) (φ : ℝ → ℝ), 0 ≤ ε → 0 ≤ M → 0 < A → 0 < t → (∫⁻ z in closedBall y (t * A) ×ˢ (univ : Set (Grassmannian N n)), ENNReal.ofReal ‖LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap z.2 - Grassmannian.projectionLinearMap P)‖ ∂W.measure) ≤ ENNReal.ofReal (ε * (t * A) ^ n) → (∀ (z : Euclidean N) (S : Grassmannian N n), |fderiv ℝ h z (Grassmannian.project S (z - y))| ≤ M * ‖LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap S - Grassmannian.projectionLinearMap P)‖ * ‖z - y‖) → (∀ s, 0 ≤ φ s ∧ φ s ≤ 1) → (∀ s, A ^ 2 ≤ s → φ s = 0) → |∫ p, φ (‖p.1 - y‖ ^ 2 / t ^ 2) * fderiv ℝ h p.1 (Grassmannian.project p.2 (p.1 - y)) ∂W.measure| ≤ M * A ^ (n + 1) * ε * t ^ (n + 1)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
