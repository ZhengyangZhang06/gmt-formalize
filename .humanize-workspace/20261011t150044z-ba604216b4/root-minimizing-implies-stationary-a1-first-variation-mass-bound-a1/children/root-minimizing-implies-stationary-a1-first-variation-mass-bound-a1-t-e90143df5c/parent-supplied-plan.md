# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.minimizing_implies_stationary-a1.first_variation_mass_bound-a1.trace_projection_frame-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-first-variation-mass-bound-a1-t-e90143df5c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.minimizing_implies_stationary-a1.first_variation_mass_bound-a1`
- Child key: `trace_projection_frame`
- Declaration: `Submission.fvmb_trace_starProjection_comp_eq_sum_inner`
- Exact Lean type: `∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (τ : Fin n → Euclid P) (B : Euclid P →L[ℝ] Euclid P), Orthonormal ℝ τ → Submodule.span ℝ (Set.range τ) = Q → LinearMap.trace ℝ (Euclid P) (Q.starProjection.toLinearMap ∘ₗ B.toLinearMap) = ∑ a, inner ℝ (τ a) (B (τ a))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
