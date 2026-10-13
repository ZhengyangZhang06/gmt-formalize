# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.harmonic_approx-a1.rescale_hypotheses-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-5ff93f9d57/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.harmonic_approx-a1`
- Child key: `rescale_hypotheses`
- Declaration: `Submission.dorag_haa_rescale_hypotheses`
- Exact Lean type: `∀ (n : ℕ) (δ R₀ : ℝ) (w : Euclid n → ℝ) (Lw : NNReal), 0 < R₀ → LipschitzWith Lw w → ∫ v in ball (0 : Euclid n) R₀, ‖fderiv ℝ w v‖ ^ 2 ≤ R₀ ^ n → (∀ ζ : Euclid n → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Euclid n) R₀ → ∀ G : ℝ, (∀ v, ‖fderiv ℝ ζ v‖ ≤ G) → |∫ v in ball (0 : Euclid n) R₀, ∑ i : Fin n, fderiv ℝ w v (EuclideanSpace.single i (1 : ℝ)) * fderiv ℝ ζ v (EuclideanSpace.single i (1 : ℝ))| ≤ δ * R₀ ^ n * G) → LipschitzWith Lw (fun y : Euclid n => R₀⁻¹ * w (R₀ • y)) ∧ ∫ v in ball (0 : Euclid n) 1, ‖fderiv ℝ (fun y : Euclid n => R₀⁻¹ * w (R₀ • y)) v‖ ^ 2 ≤ 1 ∧ ∀ ζ : Euclid n → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Euclid n) 1 → ∀ G : ℝ, (∀ v, ‖fderiv ℝ ζ v‖ ≤ G) → |∫ v in ball (0 : Euclid n) 1, ∑ i : Fin n, fderiv ℝ (fun y : Euclid n => R₀⁻¹ * w (R₀ • y)) v (EuclideanSpace.single i (1 : ℝ)) * fderiv ℝ ζ v (EuclideanSpace.single i (1 : ℝ))| ≤ δ * G`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.harmonic_approx-a1.ball_rescale-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
