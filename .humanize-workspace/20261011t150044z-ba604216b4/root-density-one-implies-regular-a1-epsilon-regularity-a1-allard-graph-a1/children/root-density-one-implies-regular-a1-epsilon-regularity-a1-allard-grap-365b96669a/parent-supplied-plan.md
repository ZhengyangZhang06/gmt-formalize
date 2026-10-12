# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-365b96669a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1`
- Child key: `harmonic_approximation`
- Declaration: `Submission.dorag_harmonic_affine_approximation`
- Exact Lean type: `∀ n : ℕ, 0 < n → ∃ C : ℝ, 0 < C ∧ ∀ ε' : ℝ, 0 < ε' → ∃ δh : ℝ, 0 < δh ∧ ∀ (R₀ : ℝ) (w : Euclid n → ℝ) (Lw : NNReal), 0 < R₀ → LipschitzWith Lw w → ∫ v in ball (0 : Euclid n) R₀, ‖fderiv ℝ w v‖ ^ 2 ≤ R₀ ^ n → (∀ ζ : Euclid n → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Euclid n) R₀ → ∀ G : ℝ, (∀ v, ‖fderiv ℝ ζ v‖ ≤ G) → |∫ v in ball (0 : Euclid n) R₀, ∑ i : Fin n, fderiv ℝ w v (EuclideanSpace.single i (1 : ℝ)) * fderiv ℝ ζ v (EuclideanSpace.single i (1 : ℝ))| ≤ δh * R₀ ^ n * G) → ∃ (a : ℝ) (b : Euclid n →L[ℝ] ℝ), ‖b‖ ≤ C ∧ |a| ≤ C * Real.sqrt ((∫ v in ball (0 : Euclid n) R₀, w v ^ 2) / R₀ ^ n) + C * Real.sqrt ε' * R₀ ∧ ∀ θ' : ℝ, 0 < θ' → θ' ≤ 1 / 4 → ∫ v in ball (0 : Euclid n) (θ' * R₀), (w v - a - b v) ^ 2 ≤ C * (ε' / θ' ^ (n + 2) + θ' ^ 2) * (θ' * R₀) ^ (n + 2)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
