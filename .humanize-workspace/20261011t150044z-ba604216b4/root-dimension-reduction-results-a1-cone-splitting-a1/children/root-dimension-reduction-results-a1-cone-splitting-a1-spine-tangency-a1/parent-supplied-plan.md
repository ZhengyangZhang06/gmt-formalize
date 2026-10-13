# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.spine_tangency-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-spine-tangency-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1`
- Child key: `spine_tangency`
- Declaration: `Submission.dimred_cs_spine_tangent_of_invariant_measure`
- Exact Lean type: `∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n) (L : Submodule ℝ (Euclid P)), 0 < n → (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → R.firstVariation X = 0) → (∀ y ∈ L, ∀ A : Set (Euclid P), MeasurableSet A → R.measure ((fun x => y + x) ⁻¹' A) = R.measure A) → (∀ lam : ℝ, 0 < lam → ∀ A : Set (Euclid P), MeasurableSet A → R.measure ((fun x => lam • x) '' A) = ENNReal.ofReal (lam ^ n) * R.measure A) → ∀ᵐ x ∂R.measure, (approxTangentPlane n R.carrier x).starProjection x = x ∧ ∀ v ∈ L, (approxTangentPlane n R.carrier x).starProjection v = v`

## Sibling prerequisites

- `root.half_space_cone_lies_in_boundary-a1.tangent_projection_aemeasurable-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
