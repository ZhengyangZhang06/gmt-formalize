# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.difference_quotient_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-differenc-488312ef14/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1`
- Child key: `difference_quotient_limit`
- Declaration: `Submission.dohr_eb_difference_quotient_limit`
- Exact Lean type: `∀ (n ℓ : ℕ) (α : ℝ) (f : Rn n → Rn ℓ) (x₀ e : Rn n) (ρ δ M : ℝ), 0 < α → α ≤ 1 → 0 < δ → ContDiffOn ℝ 1 f (ball x₀ (ρ + δ * ‖e‖)) → (∀ d : ℝ, d ≠ 0 → |d| < δ → ∀ x ∈ ball x₀ ρ, ‖d⁻¹ • (fderiv ℝ f (x + d • e) - fderiv ℝ f x)‖ ≤ M) → (∀ d : ℝ, d ≠ 0 → |d| < δ → ∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ‖d⁻¹ • (fderiv ℝ f (x + d • e) - fderiv ℝ f x) - d⁻¹ • (fderiv ℝ f (y + d • e) - fderiv ℝ f y)‖ ≤ M * ‖x - y‖ ^ α) → ContDiffOn ℝ 1 (fun x => fderiv ℝ f x e) (ball x₀ ρ) ∧ (∀ x ∈ ball x₀ ρ, ‖fderiv ℝ (fun z => fderiv ℝ f z e) x‖ ≤ M) ∧ ∀ x ∈ ball x₀ ρ, ∀ y ∈ ball x₀ ρ, ‖fderiv ℝ (fun z => fderiv ℝ f z e) x - fderiv ℝ (fun z => fderiv ℝ f z e) y‖ ≤ M * ‖x - y‖ ^ α`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
