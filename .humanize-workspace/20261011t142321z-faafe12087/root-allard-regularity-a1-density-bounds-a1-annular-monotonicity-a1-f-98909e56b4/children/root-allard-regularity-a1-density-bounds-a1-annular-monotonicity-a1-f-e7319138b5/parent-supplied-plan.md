# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.fixed_cutoff-a1.ball_integrable-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-density-bounds-a1-annular-monotonicity-a1-f-e7319138b5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1.density_bounds-a1.annular_monotonicity-a1.fixed_cutoff-a1`
- Child key: `ball_integrable`
- Declaration: `Submission.allard52_am_fc_ball_integrable`
- Exact Lean type: `∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (H : Amb n ℓ → Amb n ℓ) (w : Amb n ℓ → ℝ) (y : Amb n ℓ) (R S : ℝ), S < R → μ (closedBall y R) < ⊤ → IntegrableOn H (closedBall y R) μ → AEStronglyMeasurable w (μ.restrict (ball y R)) → (∀ᵐ x ∂μ, x ∈ ball y R → 0 ≤ w x ∧ w x ≤ 1) → IntegrableOn (fun _ => (1 : ℝ)) (closedBall y S) μ ∧ IntegrableOn (fun x => inner ℝ (x - y) (H x)) (closedBall y S) μ ∧ IntegrableOn w (closedBall y S) μ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
