# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.harmonic_approx-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-9c9f0b580c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1`
- Child key: `harmonic_approx`
- Declaration: `Submission.dorag_ha_approximation`
- Exact Lean type: `∀ n : ℕ, 0 < n → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (R₀ : ℝ) (w : Euclid n → ℝ) (Lw : NNReal), 0 < R₀ → LipschitzWith Lw w → ∫ v in ball (0 : Euclid n) R₀, ‖fderiv ℝ w v‖ ^ 2 ≤ R₀ ^ n → (∀ ζ : Euclid n → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Euclid n) R₀ → ∀ G : ℝ, (∀ v, ‖fderiv ℝ ζ v‖ ≤ G) → |∫ v in ball (0 : Euclid n) R₀, ∑ i : Fin n, fderiv ℝ w v (EuclideanSpace.single i (1 : ℝ)) * fderiv ℝ ζ v (EuclideanSpace.single i (1 : ℝ))| ≤ δ * R₀ ^ n * G) → ∃ h : Euclid n → ℝ, (∀ m : ℕ, ContDiffOn ℝ m h (ball (0 : Euclid n) R₀)) ∧ (∀ y ∈ ball (0 : Euclid n) R₀, ∑ i : Fin n, iteratedFDeriv ℝ 2 h y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0) ∧ IntegrableOn (fun y => ‖fderiv ℝ h y‖ ^ 2) (ball (0 : Euclid n) R₀) ∧ ∫ y in ball (0 : Euclid n) R₀, ‖fderiv ℝ h y‖ ^ 2 ≤ R₀ ^ n ∧ IntegrableOn (fun y => (h y - w y) ^ 2) (ball (0 : Euclid n) R₀) ∧ ∫ y in ball (0 : Euclid n) R₀, (h y - w y) ^ 2 ≤ ε * R₀ ^ (n + 2)`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.poincare_ball-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.rellich_ball-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.weyl_lemma-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.energy_lsc-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
