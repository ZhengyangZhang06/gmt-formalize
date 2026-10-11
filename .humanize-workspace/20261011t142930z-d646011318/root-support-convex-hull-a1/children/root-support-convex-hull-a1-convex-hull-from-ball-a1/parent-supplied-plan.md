# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.support_convex_hull-a1.convex_hull_from_ball-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-support-convex-hull-a1-convex-hull-from-ball-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.support_convex_hull-a1`
- Child key: `convex_hull_from_ball`
- Declaration: `Submission.convex_hull_property_of_support_in_ball`
- Exact Lean type: `SupportInBall → ConvexHullProperty`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
