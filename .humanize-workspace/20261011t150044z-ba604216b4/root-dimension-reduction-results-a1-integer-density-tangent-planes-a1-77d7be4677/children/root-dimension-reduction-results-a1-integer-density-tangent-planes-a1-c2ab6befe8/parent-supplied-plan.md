# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.planar_constancy-a1.planar_orientation_sign-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-c2ab6befe8/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.planar_constancy-a1`
- Child key: `planar_orientation_sign`
- Declaration: `Submission.idtp_pc_orient_ae_eq_or_neg`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (τ : Fin n → Euclid P), Orthonormal ℝ τ → μHE[n] (R.carrier \ (Submodule.span ℝ (Set.range τ) : Set (Euclid P))) = 0 → ∀ᵐ x ∂(μHE[n].restrict R.carrier), (∀ α : Covector (Euclid P) n, R.orient x α = α τ) ∨ (∀ α : Covector (Euclid P) n, R.orient x α = -α τ)`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.approx_tangent_in_submanifold-a1.approx_tangent_le_flat-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.orientation_sign-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
