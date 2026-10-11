# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.affine_approximation-a1.pinched_density_bounds-a1.lintegral_closed_ball_le_of_annuli-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-affine-approximation-a1-pinched-density-bounds-a1-lintegral-clos-beefa53e33/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.affine_approximation-a1.pinched_density_bounds-a1`
- Child key: `lintegral_closed_ball_le_of_annuli`
- Declaration: `Submission.aal_lintegral_closedBall_le_of_annuli`
- Exact Lean type: `∀ (n ℓ : ℕ) (μ : Measure (Amb n ℓ)) (g : Amb n ℓ → ℝ) (y : Amb n ℓ) (s M : ℝ), 0 < s → (∀ x, 0 ≤ g x) → g y = 0 → (∀ t : ℝ, 0 < t → t < s → IntegrableOn g (closedBall y s \ closedBall y t) μ ∧ ∫ x in closedBall y s \ closedBall y t, g x ∂μ ≤ M) → ∫⁻ x in closedBall y s, ENNReal.ofReal (g x) ∂μ ≤ ENNReal.ofReal M`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
