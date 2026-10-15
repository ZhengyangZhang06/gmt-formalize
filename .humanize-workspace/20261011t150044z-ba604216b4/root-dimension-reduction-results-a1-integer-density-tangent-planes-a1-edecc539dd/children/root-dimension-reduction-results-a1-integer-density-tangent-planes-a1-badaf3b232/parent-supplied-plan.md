# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.cone_set_finite_planes-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-badaf3b232/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1`
- Child key: `cone_set_finite_planes`
- Declaration: `Submission.idtp_tdc_cone_set_finite_planes`
- Exact Lean type: `∀ (P : ℕ) (S : Set (Euclid P)), IsClosed S → (∀ x ∈ S, ∀ s : ℝ, 0 < s → s • x ∈ S) → (∀ p ∈ S, p ≠ 0 → ∃ (δ : ℝ) (Q : Submodule ℝ (Euclid P)), 0 < δ ∧ Module.finrank ℝ Q = 2 ∧ S ∩ ball p δ = (Q : Set (Euclid P)) ∩ ball p δ) → ∃ (q : ℕ) (Ps : Fin q → Submodule ℝ (Euclid P)), (∀ i, Module.finrank ℝ (Ps i) = 2) ∧ (∀ i j, i ≠ j → Ps i ⊓ Ps j = ⊥) ∧ ∀ x ∈ S, x ≠ 0 → ∃ i, x ∈ Ps i`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
