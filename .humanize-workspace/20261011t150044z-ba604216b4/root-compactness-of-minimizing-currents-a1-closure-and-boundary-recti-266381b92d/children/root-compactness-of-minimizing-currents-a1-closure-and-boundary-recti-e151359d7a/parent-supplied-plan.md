# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.im_criterion-a1.tangent_field_measurable-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-e151359d7a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.im_criterion-a1`
- Child key: `tangent_field_measurable`
- Declaration: `Submission.cbr_ci_imc_tangent_field_aestronglyMeasurable`
- Exact Lean type: `∀ (P n : ℕ) (M : Set (Euclid P)) (Q : Euclid P → Submodule ℝ (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → μHE[n] (M ∩ K) ≠ ∞) → (∀ᵐ x ∂(μHE[n].restrict M), HasApproximateTangentSpaceAt n M x (Q x)) → AEStronglyMeasurable (fun x => (Q x).starProjection) (μHE[n].restrict M)`

## Sibling prerequisites

- `root.half_space_cone_lies_in_boundary-a1.tangent_projection_aemeasurable-a1.plane_quadratic_moment-a1`
- `root.half_space_cone_lies_in_boundary-a1.tangent_projection_aemeasurable-a1.blowup_integral_continuous-a1`
- `root.half_space_cone_lies_in_boundary-a1.tangent_projection_aemeasurable-a1.projection_field_aemeasurable-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
