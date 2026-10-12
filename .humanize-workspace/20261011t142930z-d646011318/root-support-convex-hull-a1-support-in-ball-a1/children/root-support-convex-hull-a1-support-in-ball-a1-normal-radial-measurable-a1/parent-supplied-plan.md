# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.support_convex_hull-a1.support_in_ball-a1.normal_radial_measurable-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-support-convex-hull-a1-support-in-ball-a1-normal-radial-measurable-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.support_convex_hull-a1.support_in_ball-a1`
- Child key: `normal_radial_measurable`
- Declaration: `Submission.aestronglyMeasurable_normalRadialSq_and_bounds`
- Exact Lean type: `∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (ξ : Ambient n ℓ), AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight → AEStronglyMeasurable (fun x ↦ V.normalRadialSq ξ x) V.weight ∧ ∀ x, 0 ≤ V.normalRadialSq ξ x ∧ V.normalRadialSq ξ x ≤ 1`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
