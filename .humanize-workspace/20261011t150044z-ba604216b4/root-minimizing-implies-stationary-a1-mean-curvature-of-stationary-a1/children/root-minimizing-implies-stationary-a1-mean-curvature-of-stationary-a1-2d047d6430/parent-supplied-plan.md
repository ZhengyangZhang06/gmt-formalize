# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.minimizing_implies_stationary-a1.mean_curvature_of_stationary-a1.first_variation_additive-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-mean-curvature-of-stationary-a1-2d047d6430/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.minimizing_implies_stationary-a1.mean_curvature_of_stationary-a1`
- Child key: `first_variation_additive`
- Declaration: `Submission.mcs_firstVariation_add`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (X Y : Euclid P → Euclid P), AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) (μHE[n].restrict R.carrier) → ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U → ContDiff ℝ 1 Y → HasCompactSupport Y → tsupport Y ⊆ U → R.firstVariation (X + Y) = R.firstVariation X + R.firstVariation Y`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
