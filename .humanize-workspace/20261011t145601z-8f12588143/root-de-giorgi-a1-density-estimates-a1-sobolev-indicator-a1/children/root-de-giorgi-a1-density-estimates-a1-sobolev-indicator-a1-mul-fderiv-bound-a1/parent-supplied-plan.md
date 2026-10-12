# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.density_estimates-a1.sobolev_indicator-a1.mul_fderiv_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-density-estimates-a1-sobolev-indicator-a1-mul-fderiv-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.density_estimates-a1.sobolev_indicator-a1`
- Child key: `mul_fderiv_bound`
- Declaration: `Submission.deGiorgiSobInd_mul_lipschitz_fderiv_bound`
- Exact Lean type: `∀ (N : ℕ) (ζ u : Rn N → ℝ) (K L : ℝ≥0), LipschitzWith K ζ → HasCompactSupport ζ → (∀ y, 0 ≤ ζ y) → LipschitzWith L u → (∀ y, 0 ≤ u y ∧ u y ≤ 1) → (∃ K' : ℝ≥0, LipschitzWith K' (fun y ↦ ζ y * u y)) ∧ HasCompactSupport (fun y ↦ ζ y * u y) ∧ ∫ y, ‖fderiv ℝ (fun y ↦ ζ y * u y) y‖ ≤ (∫ y, ζ y * ‖fderiv ℝ u y‖) + ∫ y, u y * ‖fderiv ℝ ζ y‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
