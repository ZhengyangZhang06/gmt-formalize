# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.weyl_lemma-a1.conv_laplacian-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-d4d864d018/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.weyl_lemma-a1`
- Child key: `conv_laplacian`
- Declaration: `Submission.dorag_ha_weyl_conv_laplacian`
- Exact Lean type: `∀ (n : ℕ) (f φ : Euclid n → ℝ), LocallyIntegrable f → (∀ m : ℕ, ContDiff ℝ m φ) → HasCompactSupport φ → (∀ m : ℕ, ContDiff ℝ m (fun x => ∫ y, f y * φ (x - y))) ∧ ∀ x : Euclid n, ∑ i : Fin n, iteratedFDeriv ℝ 2 (fun x => ∫ y, f y * φ (x - y)) x ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = ∫ y, f y * ∑ i : Fin n, iteratedFDeriv ℝ 2 φ (x - y) ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)]`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
