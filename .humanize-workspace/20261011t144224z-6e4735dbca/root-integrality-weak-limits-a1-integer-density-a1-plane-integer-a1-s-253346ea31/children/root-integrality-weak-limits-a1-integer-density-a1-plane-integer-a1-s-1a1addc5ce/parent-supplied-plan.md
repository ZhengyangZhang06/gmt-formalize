# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.slice_selection-a1.fatou_level_selection-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-plane-integer-a1-s-1a1addc5ce/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.integer_density-a1.plane_integer-a1.slice_selection-a1`
- Child key: `fatou_level_selection`
- Declaration: `Submission.ind_pi_ss_fatou_level_selection`
- Exact Lean type: `∀ (g : ℕ → ℝ → ℝ≥0∞) (a b : ℝ) (C : ℝ≥0∞) (E : Set ℝ), a < b → (∀ k, Measurable (g k)) → C < ∞ → (∀ k, ∫⁻ t in Ioo a b, g k t ≤ C) → E.Countable → ∃ (γ : ℝ) (σ : ℕ → ℕ) (G : ℝ≥0∞), γ ∈ Ioo a b ∧ γ ∉ E ∧ StrictMono σ ∧ G < ∞ ∧ ∀ k, g (σ k) γ ≤ G`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
