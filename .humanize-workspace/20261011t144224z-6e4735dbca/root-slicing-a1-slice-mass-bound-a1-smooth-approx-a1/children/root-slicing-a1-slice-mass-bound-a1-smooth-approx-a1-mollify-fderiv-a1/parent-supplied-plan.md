# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_mass_bound-a1.smooth_approx-a1.mollify_fderiv-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-smooth-approx-a1-mollify-fderiv-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_mass_bound-a1.smooth_approx-a1`
- Child key: `mollify_fderiv`
- Declaration: `Submission.slicing_mb_sa_mollify_lipschitz_hasFDerivAt`
- Exact Lean type: `∀ (P : ℕ) (F : Eucl P → ℝ) (L : ℝ≥0), LipschitzWith L F → ∀ ρ : Eucl P → ℝ, Continuous ρ → HasCompactSupport ρ → ∀ x : Eucl P, HasFDerivAt (fun x' : Eucl P => ∫ y, ρ y * F (x' - y)) (∫ y, ρ y • fderiv ℝ F (x - y)) x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
