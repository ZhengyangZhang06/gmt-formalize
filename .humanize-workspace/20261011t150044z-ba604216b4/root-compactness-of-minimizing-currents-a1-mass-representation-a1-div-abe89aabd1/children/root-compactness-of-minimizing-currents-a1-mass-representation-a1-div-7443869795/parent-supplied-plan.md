# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.mass_representation-a1.divergence_form-a1.jacobi_trace-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-div-7443869795/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.divergence_form-a1`
- Child key: `jacobi_trace`
- Declaration: `Submission.cmr_df_det_update_sum_trace`
- Exact Lean type: `∀ (n : ℕ) (A : Euclid n →ₗ[ℝ] Euclid n) (u : Fin n → Euclid n), ∑ i : Fin n, Matrix.det (Matrix.of fun k j => Function.update u i (A (u i)) j k) = LinearMap.trace ℝ (Euclid n) A * Matrix.det (Matrix.of fun k j => u j k)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
