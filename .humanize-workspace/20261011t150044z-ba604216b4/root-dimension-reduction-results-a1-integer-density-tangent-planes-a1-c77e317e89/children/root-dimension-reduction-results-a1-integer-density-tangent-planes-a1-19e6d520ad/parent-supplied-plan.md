# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_tangent_cone_planar-a1.blowup_translation_invariance-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-19e6d520ad/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_tangent_cone_planar-a1`
- Child key: `blowup_translation_invariance`
- Declaration: `Submission.idtp_cttp_blowup_limit_translation_invariant`
- Exact Lean type: `∀ (P n : ℕ) (C C' : GeometricCurrentOn (univ : Set (Euclid P)) n) (p : Euclid P) (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j), IsIntegerMultiplicity C → IsConeCurrent C → Tendsto lams atTop (𝓝 0) → MassMeasuresConverge (fun j => blowUp C p (lams j) (hlams j).ne') C' → ∀ R' : IMRep (univ : Set (Euclid P)) n, R'.Represents C' → ∀ v ∈ Submodule.span ℝ {p}, ∀ A : Set (Euclid P), MeasurableSet A → R'.measure ((fun x => x + v) ⁻¹' A) = R'.measure A`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
