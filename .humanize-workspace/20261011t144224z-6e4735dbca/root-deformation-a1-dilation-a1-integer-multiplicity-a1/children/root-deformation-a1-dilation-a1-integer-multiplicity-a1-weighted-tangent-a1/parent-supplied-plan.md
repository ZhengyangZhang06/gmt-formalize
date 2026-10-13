# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.dilation-a1.integer_multiplicity-a1.weighted_tangent-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-dilation-a1-integer-multiplicity-a1-weighted-tangent-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.dilation-a1.integer_multiplicity-a1`
- Child key: `weighted_tangent`
- Declaration: `Submission.deformation_dilation_im_weightedTangent`
- Exact Lean type: `∀ (N k : ℕ) (ρ : ℝ) (M : Set (Eucl N)) (θ : Eucl N → ℝ) (x : Eucl N) (Q : Submodule ℝ (Eucl N)), 0 < ρ → HasWeightedApproximateTangentSpaceAt k M θ x Q → HasWeightedApproximateTangentSpaceAt k ((fun y : Eucl N => ρ • y) '' M) (fun y : Eucl N => θ (ρ⁻¹ • y)) (ρ • x) Q`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
