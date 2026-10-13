# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.tangent_locality-a1.ae_l1_density-a1.ball_reduction-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-tangent-locality-a1-ae-l1-density-a1-ball-reduction-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1.tangent_locality-a1.ae_l1_density-a1`
- Child key: `ball_reduction`
- Declaration: `Submission.fiw_tl_ald_ball_reduction`
- Exact Lean type: `∀ (P : ℕ) (μ : Measure (Eucl P)) (U A : Set (Eucl P)) (Φ : Eucl P → Prop), IsOpen U → A ⊆ U → (∀ (y : Eucl P) (r : ℝ), closedBall y r ⊆ U → ∀ᵐ x ∂(μ.restrict (A ∩ ball y r)), Φ x) → ∀ᵐ x ∂(μ.restrict A), Φ x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
