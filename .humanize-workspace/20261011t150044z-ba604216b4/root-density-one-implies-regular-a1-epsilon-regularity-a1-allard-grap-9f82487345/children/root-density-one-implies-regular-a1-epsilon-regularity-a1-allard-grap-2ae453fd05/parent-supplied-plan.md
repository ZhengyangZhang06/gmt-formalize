# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.mean_value-a1.green_identity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-2ae453fd05/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.harmonic_approximation-a1.mean_value-a1`
- Child key: `green_identity`
- Declaration: `Submission.dorag_ha_mv_green_identity`
- Exact Lean type: `∀ (n : ℕ) (V : Set (Euclid n)) (G Ψ : Euclid n → ℝ), IsOpen V → ContDiffOn ℝ 2 G V → ContDiff ℝ 1 Ψ → HasCompactSupport Ψ → tsupport Ψ ⊆ V → ∫ y : Euclid n, ∑ i : Fin n, fderiv ℝ Ψ y (EuclideanSpace.single i (1 : ℝ)) * fderiv ℝ G y (EuclideanSpace.single i (1 : ℝ)) = -∫ y : Euclid n, Ψ y * ∑ i : Fin n, iteratedFDeriv ℝ 2 G y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)]`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
