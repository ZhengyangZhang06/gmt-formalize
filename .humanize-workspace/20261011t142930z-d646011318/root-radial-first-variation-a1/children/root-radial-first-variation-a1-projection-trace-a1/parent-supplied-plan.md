# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.radial_first_variation-a1.projection_trace-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-radial-first-variation-a1-projection-trace-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.radial_first_variation-a1`
- Child key: `projection_trace`
- Declaration: `Submission.trace_scalar_add_rankOne_comp_starProjection`
- Exact Lean type: `∀ (n ℓ : ℕ) (P : Submodule ℝ (Ambient n ℓ)) (c : ℝ) (F : Ambient n ℓ →L[ℝ] ℝ) (v : Ambient n ℓ), LinearMap.trace ℝ (Ambient n ℓ) ((c • ContinuousLinearMap.id ℝ (Ambient n ℓ) + F.smulRight v).toLinearMap ∘ₗ P.starProjection.toLinearMap) = c * (Module.finrank ℝ P : ℝ) + F (P.starProjection v)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
