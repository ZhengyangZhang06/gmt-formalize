# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tangent_structure-a1.blowup_density-a1.cutoff_ball_bounds-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-blowup-density-a1-cutoff-ball-bounds-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tangent_structure-a1.blowup_density-a1`
- Child key: `cutoff_ball_bounds`
- Declaration: `Submission.ts_blowup_cutoff_closedBall_bounds`
- Exact Lean type: `∀ (n ℓ : ℕ) (μ : Measure (Ambient n ℓ)) (x : Ambient n ℓ) (f : C_c(Ambient n ℓ, ℝ)) (t : ℝ), IsFiniteMeasureOnCompacts μ → 0 < t → ((∀ y : Ambient n ℓ, f y ≤ 1) → (∀ y : Ambient n ℓ, 1 < ‖y‖ → f y ≤ 0) → ∫ y, f (t⁻¹ • (y - x)) ∂μ ≤ μ.real (closedBall x t)) ∧ ((∀ y : Ambient n ℓ, 0 ≤ f y) → (∀ y : Ambient n ℓ, ‖y‖ ≤ 1 → 1 ≤ f y) → μ.real (closedBall x t) ≤ ∫ y, f (t⁻¹ • (y - x)) ∂μ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
