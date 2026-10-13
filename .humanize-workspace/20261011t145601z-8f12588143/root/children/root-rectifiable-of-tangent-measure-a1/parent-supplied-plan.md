# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rectifiable_of_tangent_measure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-rectifiable-of-tangent-measure-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root`
- Child key: `rectifiable_of_tangent_measure`
- Declaration: `Submission.rectifiable_of_approx_tangent_measure`
- Exact Lean type: `∀ (n ℓ : ℕ) (μ : Measure (Rn (n + ℓ))), (∀ K : Set (Rn (n + ℓ)), IsCompact K → μ K < ∞) → (∀ᵐ x ∂μ, ∃ (P : Submodule ℝ (Rn (n + ℓ))) (θ : ℝ), 0 < θ ∧ HasApproxTangentPlaneWithMultiplicity n μ x P θ) → ∃ R : Set (Rn (n + ℓ)), MeasurableSet R ∧ CountablyRectifiable n R ∧ μ Rᶜ = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
