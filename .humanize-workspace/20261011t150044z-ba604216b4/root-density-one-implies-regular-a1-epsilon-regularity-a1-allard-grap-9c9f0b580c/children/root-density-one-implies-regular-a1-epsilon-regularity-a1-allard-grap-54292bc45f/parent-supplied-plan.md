# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.harmonic_approx-a1.rescale_conclusion-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-54292bc45f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.harmonic_approx-a1`
- Child key: `rescale_conclusion`
- Declaration: `Submission.dorag_haa_rescale_conclusion`
- Exact Lean type: `∀ (n : ℕ) (ε R₀ : ℝ) (w h₁ : Euclid n → ℝ), 0 < R₀ → (∀ m : ℕ, ContDiffOn ℝ m h₁ (ball (0 : Euclid n) 1)) → (∀ y ∈ ball (0 : Euclid n) 1, ∑ i : Fin n, iteratedFDeriv ℝ 2 h₁ y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0) → IntegrableOn (fun y => ‖fderiv ℝ h₁ y‖ ^ 2) (ball (0 : Euclid n) 1) → ∫ y in ball (0 : Euclid n) 1, ‖fderiv ℝ h₁ y‖ ^ 2 ≤ 1 → IntegrableOn (fun y => (h₁ y - R₀⁻¹ * w (R₀ • y)) ^ 2) (ball (0 : Euclid n) 1) → ∫ y in ball (0 : Euclid n) 1, (h₁ y - R₀⁻¹ * w (R₀ • y)) ^ 2 ≤ ε → ∃ h : Euclid n → ℝ, (∀ m : ℕ, ContDiffOn ℝ m h (ball (0 : Euclid n) R₀)) ∧ (∀ y ∈ ball (0 : Euclid n) R₀, ∑ i : Fin n, iteratedFDeriv ℝ 2 h y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0) ∧ IntegrableOn (fun y => ‖fderiv ℝ h y‖ ^ 2) (ball (0 : Euclid n) R₀) ∧ ∫ y in ball (0 : Euclid n) R₀, ‖fderiv ℝ h y‖ ^ 2 ≤ R₀ ^ n ∧ IntegrableOn (fun y => (h y - w y) ^ 2) (ball (0 : Euclid n) R₀) ∧ ∫ y in ball (0 : Euclid n) R₀, (h y - w y) ^ 2 ≤ ε * R₀ ^ (n + 2)`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.harmonic_approx-a1.ball_rescale-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
