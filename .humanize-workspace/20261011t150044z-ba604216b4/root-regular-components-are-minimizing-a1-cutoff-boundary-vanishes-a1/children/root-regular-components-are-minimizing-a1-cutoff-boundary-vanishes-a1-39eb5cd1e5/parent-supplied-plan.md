# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_components_are_minimizing-a1.cutoff_boundary_vanishes-a1.null_compact_ball_cover-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-cutoff-boundary-vanishes-a1-39eb5cd1e5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_components_are_minimizing-a1.cutoff_boundary_vanishes-a1`
- Child key: `null_compact_ball_cover`
- Declaration: `Submission.regcomp_null_compact_ball_cover`
- Exact Lean type: `∀ (P m : ℕ) (Z : Set (Euclid P)), IsCompact Z → μH[(m : ℝ)] Z = 0 → ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∃ (J : ℕ) (p : Fin J → Euclid P) (σ : Fin J → ℝ), (∀ j, p j ∈ Z) ∧ (∀ j, 0 < σ j ∧ σ j < δ) ∧ Z ⊆ ⋃ j, ball (p j) (σ j) ∧ ∑ j, σ j ^ m < ε`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
