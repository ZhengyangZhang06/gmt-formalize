# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.harmonic_approx-a1.weakly_harmonic_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-4cc16165a0/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.harmonic_approx-a1`
- Child key: `weakly_harmonic_limit`
- Declaration: `Submission.dorag_haa_weakly_harmonic_limit`
- Exact Lean type: `∀ (n : ℕ) (R : ℝ) (u : ℕ → Euclid n → ℝ) (c δ : ℕ → ℝ) (W : Euclid n → ℝ), (∀ j, ∃ L : NNReal, LipschitzWith L (u j)) → Tendsto δ atTop (𝓝 0) → MemLp W 2 (volume.restrict (ball (0 : Euclid n) R)) → Tendsto (fun j => ∫ x in ball (0 : Euclid n) R, (u j x - c j - W x) ^ 2) atTop (𝓝 0) → (∀ (j : ℕ) (ζ : Euclid n → ℝ), ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Euclid n) R → ∀ G : ℝ, (∀ v, ‖fderiv ℝ ζ v‖ ≤ G) → |∫ v in ball (0 : Euclid n) R, ∑ i : Fin n, fderiv ℝ (u j) v (EuclideanSpace.single i (1 : ℝ)) * fderiv ℝ ζ v (EuclideanSpace.single i (1 : ℝ))| ≤ δ j * G) → ∀ ζ : Euclid n → ℝ, ContDiff ℝ 2 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Euclid n) R → ∫ y in ball (0 : Euclid n) R, W y * ∑ i : Fin n, iteratedFDeriv ℝ 2 ζ y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.harmonic_approx-a1.lipschitz_ibp-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.harmonic_approx-a1.l2_pairing-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
