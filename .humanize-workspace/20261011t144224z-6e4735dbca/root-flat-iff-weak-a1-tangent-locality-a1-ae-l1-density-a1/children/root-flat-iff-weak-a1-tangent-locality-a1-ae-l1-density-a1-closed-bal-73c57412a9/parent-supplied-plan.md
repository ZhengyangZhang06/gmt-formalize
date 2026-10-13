# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.tangent_locality-a1.ae_l1_density-a1.closed_ball_lebesgue_point-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-tangent-locality-a1-ae-l1-density-a1-closed-bal-73c57412a9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1.tangent_locality-a1.ae_l1_density-a1`
- Child key: `closed_ball_lebesgue_point`
- Declaration: `Submission.fiw_tl_ald_closedBall_lebesgue_point`
- Exact Lean type: `∀ (P : ℕ) (ν : Measure (Eucl P)) [IsFiniteMeasure ν] (g : Eucl P → ℝ), Integrable g ν → ∀ᵐ x ∂ν, Tendsto (fun s : ℝ => (∫⁻ z in closedBall x s, ‖g z - g x‖ₑ ∂ν) / ν (closedBall x s)) (𝓝[>] 0) (𝓝 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
