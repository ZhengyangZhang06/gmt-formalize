# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.mass_representation-a1.divergence_form-a1.coordinate_trace-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-div-c9e202e0ac/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.divergence_form-a1`
- Child key: `coordinate_trace`
- Declaration: `Submission.cmr_df_cons_sum_trace`
- Exact Lean type: `∀ (P m : ℕ) (I : Fin (m + 1) → Fin P) (θ : Covector (Euclid P) (m + 1)) (A : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) (L : Euclid P → Euclid P), (∀ v : Fin (m + 1) → Euclid P, θ v = Matrix.det (Matrix.of fun k j => v j (I k))) → (∀ (v : Euclid P) (k : Fin (m + 1)), L v (I k) = A (WithLp.toLp 2 (fun k' => v (I k'))) k) → ∀ w : Fin (m + 1) → Euclid P, ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) * θ (Fin.cons (L (w i)) (i.removeNth w)) = LinearMap.trace ℝ (Euclid (m + 1)) A * θ w`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.mass_representation-a1.divergence_form-a1.jacobi_trace-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
