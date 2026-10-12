# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_components_are_minimizing-a1.cutoff_boundary_vanishes-a1.smooth_cutoff_product-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-cutoff-boundary-vanishes-a1-85ef8f52bf/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_components_are_minimizing-a1.cutoff_boundary_vanishes-a1`
- Child key: `smooth_cutoff_product`
- Declaration: `Submission.regcomp_smooth_cutoff_product`
- Exact Lean type: `∀ (P : ℕ), ∃ c₀ : ℝ, 0 ≤ c₀ ∧ ∀ (J : ℕ) (p : Fin J → Euclid P) (σ : Fin J → ℝ), (∀ j, 0 < σ j) → ∃ ζ : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ ∧ (∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1) ∧ (∀ j, ∀ x ∈ ball (p j) (σ j), ζ x = 0) ∧ (∀ x, 1 - ζ x ≤ ∑ j, (ball (p j) (2 * σ j)).indicator (fun _ => (1 : ℝ)) x) ∧ ∀ x, ‖fderiv ℝ ζ x‖ ≤ ∑ j, (ball (p j) (2 * σ j)).indicator (fun _ => c₀ / σ j) x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
