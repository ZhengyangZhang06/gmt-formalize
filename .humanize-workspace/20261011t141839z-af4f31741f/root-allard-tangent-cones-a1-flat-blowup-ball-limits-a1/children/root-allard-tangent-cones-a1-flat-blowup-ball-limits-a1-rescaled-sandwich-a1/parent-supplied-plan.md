# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_tangent_cones-a1.flat_blowup_ball_limits-a1.rescaled_sandwich-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-flat-blowup-ball-limits-a1-rescaled-sandwich-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_tangent_cones-a1.flat_blowup_ball_limits-a1`
- Child key: `rescaled_sandwich`
- Declaration: `Submission.allard_tc_fbl_rescaled_sandwich`
- Exact Lean type: `∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (x : Euclidean N) (β : C(Grassmannian N n, ℝ)) (r : ℝ) (k : ℕ), 0 < r → closedBall x (2 * r) ⊆ U → (∀ S, 0 ≤ β S) → (∫ z, min 1 (((k : ℝ) + 1) * max 0 (1 - ‖z.1‖)) * β z.2 ∂(rescaledMeasure V x r)) ≤ (∫ z in closedBall x r ×ˢ (univ : Set (Grassmannian N n)), β z.2 ∂V.measure) / r ^ n ∧ (∫ z in closedBall x r ×ˢ (univ : Set (Grassmannian N n)), β z.2 ∂V.measure) / r ^ n ≤ ∫ z, max 0 (1 - ((k : ℝ) + 1) * max 0 (‖z.1‖ - 1)) * β z.2 ∂(rescaledMeasure V x r)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
