# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.allard_lemma-a1.weighted_radial_monotonicity-a1.first_variation_lower_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1-weighted-radial-monotoni-80029abc20/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.allard_lemma-a1.weighted_radial_monotonicity-a1`
- Child key: `first_variation_lower_bound`
- Declaration: `Submission.intcpt_allard_wrm_first_variation_lower_bound`
- Exact Lean type: `∀ (N n : ℕ) (U : Set (Euclidean N)) (W : Varifold N n U) (y : Euclidean N) (h : Euclidean N → ℝ) (φ : ℝ → ℝ) (A t : ℝ), (∀ (a : Euclidean N → ℝ) (c z : Euclidean N) (S : Grassmannian N n), DifferentiableAt ℝ a z → Varifold.tangentialDivergence (fun w ↦ a w • (w - c)) z S = n * a z + fderiv ℝ a z (Grassmannian.project S (z - c))) → ContDiff ℝ 1 h → (∀ z, 0 ≤ h z) → ContDiff ℝ 1 φ → Antitone φ → 0 < A → (∀ s, A ^ 2 ≤ s → φ s = 0) → 0 < t → closedBall y (t * A) ⊆ U → (n : ℝ) * (∫ z, φ (‖z - y‖ ^ 2 / t ^ 2) * h z ∂W.weight) - t * (∫ z, deriv φ (‖z - y‖ ^ 2 / t ^ 2) * (-2 * ‖z - y‖ ^ 2 / t ^ 3) * h z ∂W.weight) + (∫ p, φ (‖p.1 - y‖ ^ 2 / t ^ 2) * fderiv ℝ h p.1 (Grassmannian.project p.2 (p.1 - y)) ∂W.measure) ≤ W.firstVariation (fun z ↦ (h z * φ (‖z - y‖ ^ 2 / t ^ 2)) • (z - y))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
