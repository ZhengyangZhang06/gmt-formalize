# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tangent_structure-a1.approx_tangent_unique-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-approx-tangent-unique-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tangent_structure-a1`
- Child key: `approx_tangent_unique`
- Declaration: `Submission.ts_approx_tangent_plane_unique`
- Exact Lean type: `∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (x : Ambient n ℓ) (P Q : Submodule ℝ (Ambient n ℓ)), V.IsApproxTangentAt x P → V.IsApproxTangentAt x Q → P = Q`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
