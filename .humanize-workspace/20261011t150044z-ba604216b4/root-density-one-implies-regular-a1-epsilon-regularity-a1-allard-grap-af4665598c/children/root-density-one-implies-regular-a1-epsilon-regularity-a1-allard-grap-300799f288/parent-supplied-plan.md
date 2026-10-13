# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.proj_algebra-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-300799f288/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1`
- Child key: `proj_algebra`
- Declaration: `Submission.dorag_tes_projection_algebra`
- Exact Lean type: `∀ (N : ℕ), (∀ (A : Euclid N →L[ℝ] Euclid N) (y : Euclid N), ‖A y‖ ^ 2 ≤ (∑ i : Fin N, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * ‖y‖ ^ 2) ∧ (∀ Q S T : Submodule ℝ (Euclid N), ∑ i : Fin N, ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) - T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 ≤ 2 * ∑ i : Fin N, ‖Q.starProjection (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 + 2 * ∑ i : Fin N, ‖Q.starProjection (EuclideanSpace.single i (1 : ℝ)) - T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∧ (∀ (Q T : Submodule ℝ (Euclid N)) (a b : Euclid N), a ∈ T → b ∈ T → |inner ℝ (Q.starProjection a) b - inner ℝ a b| ≤ (∑ i : Fin N, ‖Q.starProjection (EuclideanSpace.single i (1 : ℝ)) - T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * ‖a‖ * ‖b‖) ∧ ∀ (Q T : Submodule ℝ (Euclid N)) (e : Euclid N), e ∈ Tᗮ → ‖Q.starProjection e‖ ^ 2 ≤ (∑ i : Fin N, ‖Q.starProjection (EuclideanSpace.single i (1 : ℝ)) - T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * ‖e‖ ^ 2`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
