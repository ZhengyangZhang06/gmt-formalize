# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.smooth_to_c1_tests-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-d2f9caa6a3/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1`
- Child key: `smooth_to_c1_tests`
- Declaration: `Submission.dgcr_smooth_tests_to_C1_tests`
- Exact Lean type: `∀ (n : ℕ) (D : Set (Euclid n)) (G : Euclid n → ℝ), IsOpen D → LocallyIntegrableOn G D volume → (∀ a : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) a → HasCompactSupport a → tsupport a ⊆ D → ∀ j : Fin n, ∫ v in D, G v * fderiv ℝ a v (EuclideanSpace.single j (1 : ℝ)) = 0) → ∀ φ : Euclid n → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∀ i : Fin n, ∫ x, G x * fderiv ℝ φ x ((EuclideanSpace.basisFun (Fin n) ℝ) i) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
