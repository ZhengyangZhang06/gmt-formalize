# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.restriction_limit-a1.helly_selection-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-restriction-limit-a1-helly-selection-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.restriction_limit-a1`
- Child key: `helly_selection`
- Declaration: `Submission.iwl_rl_monotone_helly_selection`
- Exact Lean type: `∀ (F : ℕ → ℝ → ℝ) (C : ℝ), (∀ j, Monotone (F j)) → (∀ j t, |F j t| ≤ C) → ∃ (ψ : ℕ → ℕ) (E : Set ℝ), StrictMono ψ ∧ E.Countable ∧ ∀ s ∉ E, ∀ ε : ℝ, 0 < ε → ∃ a b : ℝ, a < s ∧ s < b ∧ ∀ᶠ j in atTop, F (ψ j) b - F (ψ j) a < ε`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
