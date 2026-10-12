# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.sobolev_inequality-a1.good_radius_calculus-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-sobolev-inequality-a1-good-radius-calculus-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.sobolev_inequality-a1`
- Child key: `good_radius_calculus`
- Declaration: `Submission.sobolev_good_radius_calculus`
- Exact Lean type: `∀ (n : ℕ) (f k : ℝ → ℝ) (F : ℝ), 2 ≤ n → MonotoneOn f (Ioi 0) → MonotoneOn k (Ioi 0) → (∀ τ : ℝ, 0 < τ → 0 ≤ f τ ∧ f τ ≤ F) → (∀ τ : ℝ, 0 < τ → 0 ≤ k τ) → (∀ s r : ℝ, 0 < s → s ≤ r → f s / s ^ n ≤ f r / r ^ n + ∫ τ in Ioc s r, k τ / τ ^ n) → (∀ η : ℝ, η < 1 → ∃ᶠ s in 𝓝[>] (0 : ℝ), η < f s / s ^ n) → 0 < F ∧ ∃ r : ℝ, 0 < r ∧ r < 2 * F ^ (n : ℝ)⁻¹ ∧ f (5 * r) ≤ 5 ^ n * F ^ (n : ℝ)⁻¹ * k r`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
