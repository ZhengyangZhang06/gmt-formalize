# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.rotation_conservation-a1.test_function-a1.product_fderiv-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-58d0f2b0e9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.rotation_conservation-a1.test_function-a1`
- Child key: `product_fderiv`
- Declaration: `Submission.idtp_cse_rc_tf_product_fderiv`
- Exact Lean type: `∀ (P : ℕ) (f ζ : Euclid P → ℝ) (ψ l : ℝ → ℝ) (x v : Euclid P), x ≠ 0 → inner ℝ x v = 0 → DifferentiableAt ℝ f x → DifferentiableAt ℝ ψ (f x) → DifferentiableAt ℝ l ‖x‖ → DifferentiableAt ℝ ζ x → fderiv ℝ (fun y : Euclid P => ψ (f y) * l ‖y‖ * ζ y) x v = ψ (f x) * l ‖x‖ * fderiv ℝ ζ x v + ζ x * l ‖x‖ * (deriv ψ (f x) * fderiv ℝ f x v)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
