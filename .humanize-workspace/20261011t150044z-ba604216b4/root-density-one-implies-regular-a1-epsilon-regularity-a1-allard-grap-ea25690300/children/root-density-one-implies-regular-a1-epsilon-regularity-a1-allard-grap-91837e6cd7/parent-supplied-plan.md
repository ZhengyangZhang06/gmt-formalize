# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.weyl_lemma-a1.mollify_harmonic-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-91837e6cd7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.weyl_lemma-a1`
- Child key: `mollify_harmonic`
- Declaration: `Submission.dorag_ha_weyl_mollify_harmonic`
- Exact Lean type: `∀ (n : ℕ) (R ε : ℝ) (W φ : Euclid n → ℝ), 0 < ε → IntegrableOn W (ball (0 : Euclid n) R) → (∀ ζ : Euclid n → ℝ, ContDiff ℝ 2 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Euclid n) R → ∫ y in ball (0 : Euclid n) R, W y * ∑ i : Fin n, iteratedFDeriv ℝ 2 ζ y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0) → (∀ m : ℕ, ContDiff ℝ m φ) → (∀ y : Euclid n, ε ≤ ‖y‖ → φ y = 0) → (∀ m : ℕ, ContDiff ℝ m (fun x => ∫ y, (ball (0 : Euclid n) R).indicator W y * φ (x - y))) ∧ ∀ x ∈ ball (0 : Euclid n) (R - ε), ∑ i : Fin n, iteratedFDeriv ℝ 2 (fun x => ∫ y, (ball (0 : Euclid n) R).indicator W y * φ (x - y)) x ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.weyl_lemma-a1.conv_laplacian-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
