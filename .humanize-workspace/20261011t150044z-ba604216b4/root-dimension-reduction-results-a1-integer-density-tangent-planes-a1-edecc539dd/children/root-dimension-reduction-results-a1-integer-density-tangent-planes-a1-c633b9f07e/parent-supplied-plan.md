# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.cone_dilation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-c633b9f07e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1`
- Child key: `cone_dilation`
- Declaration: `Submission.idtp_tdc_cone_dilation`
- Exact Lean type: `∀ (P n : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) n), IsIntegerMultiplicity C → IsConeCurrent C → ∀ s : ℝ, 0 < s → (∀ W : Set (Euclid P), C.massOn ((fun x => s • x) '' W) = ENNReal.ofReal (s ^ n) * C.massOn W) ∧ (∀ x : Euclid P, s • x ∈ C.support ↔ x ∈ C.support) ∧ ∀ (x : Euclid P) (θ : ℝ), HasMassDensity C (s • x) θ ↔ HasMassDensity C x θ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
