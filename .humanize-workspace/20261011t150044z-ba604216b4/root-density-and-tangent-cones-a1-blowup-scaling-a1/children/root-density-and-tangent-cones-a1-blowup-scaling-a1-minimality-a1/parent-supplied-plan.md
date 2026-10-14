# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_scaling-a1.minimality-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-scaling-a1-minimality-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_scaling-a1`
- Child key: `minimality`
- Declaration: `Submission.dtc_blowUp_isMinimizingIn`
- Exact Lean type: `∀ (P n : ℕ) (U A : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam), IsMinimizingIn T A → IsMinimizingIn (blowUp T x lam hlam.ne') (dilation x lam '' A)`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.blowup_scaling-a1.mass_scaling-a1`
- `root.density_and_tangent_cones-a1.blowup_scaling-a1.rep_pushforward-a1`
- `root.density_and_tangent_cones-a1.blowup_scaling-a1.blowup_structure-a1`
- `root.density_and_tangent_cones-a1.blowup_scaling-a1.blowup_preimage-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
