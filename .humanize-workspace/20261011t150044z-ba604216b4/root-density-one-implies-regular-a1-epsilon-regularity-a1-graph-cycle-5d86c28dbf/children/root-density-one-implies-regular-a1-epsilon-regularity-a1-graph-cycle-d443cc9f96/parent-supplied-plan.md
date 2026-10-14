# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.boundary_weak_derivatives-a1.coordinate_form-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-d443cc9f96/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.boundary_weak_derivatives-a1`
- Child key: `coordinate_form`
- Declaration: `Submission.dgcr_bwd_coordinate_form`
- Exact Lean type: `∀ (m : ℕ) (a : Euclid (m + 1) → ℝ) (j : Fin (m + 1)), ContDiff ℝ (⊤ : ℕ∞) a → ∃ ψ : DifferentialForm (Euclid (m + 1)) m, IsSmoothForm ψ ∧ tsupport ψ ⊆ tsupport a ∧ ∀ x : Euclid (m + 1), exteriorDerivative ψ x (fun i => EuclideanSpace.single i (1 : ℝ)) = fderiv ℝ a x (EuclideanSpace.single j (1 : ℝ))`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.boundary_weak_derivatives-a1.coordinate_covector-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.boundary_weak_derivatives-a1.extderiv_smul_const-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
