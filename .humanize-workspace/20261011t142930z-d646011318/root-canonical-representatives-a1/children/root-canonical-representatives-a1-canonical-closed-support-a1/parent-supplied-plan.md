# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.canonical_representatives-a1.canonical_closed_support-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-canonical-representatives-a1-canonical-closed-support-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.canonical_representatives-a1`
- Child key: `canonical_closed_support`
- Declaration: `Submission.canonicalCarrier_closed_support`
- Exact Lean type: `ApproxTangentAE → ∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)), 0 < n → IsOpen U → (∀ ξ ∈ U, V.HasDensityAt ξ (V.density ξ)) → UpperSemicontinuousOn V.density U → (∀ α : ℝ, 0 < α → ∃ C, IsClosed C ∧ {x | x ∈ V.canonicalCarrier U ∧ α ≤ V.density x} = C ∩ U) ∧ ∀ α : ℝ, 0 < α → V.MultiplicityGE α U → V.canonicalCarrier U = V.support ∩ U ∧ ∀ x ∈ V.canonicalCarrier U, α ≤ V.density x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
