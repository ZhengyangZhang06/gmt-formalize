# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.minimizing_implies_stationary-a1.mean_curvature_of_stationary-a1.mean_curvature_field-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-mean-curvature-of-stationary-a1-85ac98219a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.minimizing_implies_stationary-a1.mean_curvature_of_stationary-a1`
- Child key: `mean_curvature_field`
- Declaration: `Submission.mcs_exists_meanCurvature_field`
- Exact Lean type: `∀ (P : ℕ) (μ : Measure (Euclid P)) (U N O : Set (Euclid P)) (pr p : Euclid P → (Euclid P →L[ℝ] Euclid P)), IsOpen U → IsOpen O → N ⊆ O → ContDiffOn ℝ 1 pr O → (closure N \ N) ∩ U = ∅ → AEStronglyMeasurable p μ → (∀ x, ‖p x‖ ≤ 1) → ∃ H : Euclid P → Euclid P, AEStronglyMeasurable H μ ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∃ Λ : ℝ, ∀ x ∈ K, ‖H x‖ ≤ Λ) ∧ ∀ x ∈ N ∩ U, H x = ∑ j : Fin P, ContinuousLinearMap.adjoint (fderiv ℝ pr x (p x (EuclideanSpace.single j 1))) (p x (EuclideanSpace.single j 1))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
