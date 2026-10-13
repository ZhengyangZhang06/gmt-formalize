# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.total_boundedness-a1.translation_estimate-a1.l1_duality-a1.compact_sign_approx-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1-translation-estimate-a1-l1-67826f76cb/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1.total_boundedness-a1.translation_estimate-a1.l1_duality-a1`
- Child key: `compact_sign_approx`
- Declaration: `Submission.fiw_tb_te_l1d_compact_sign_approx`
- Exact Lean type: `∀ (n : ℕ) (w : Eucl n → ℝ), Integrable w → ∀ ε : ℝ, 0 < ε → ∃ K₁ K₂ : Set (Eucl n), IsCompact K₁ ∧ IsCompact K₂ ∧ Disjoint K₁ K₂ ∧ ∀ g : Eucl n → ℝ, AEStronglyMeasurable g → (∀ x, |g x| ≤ 1) → (∀ x ∈ K₁, g x = 1) → (∀ x ∈ K₂, g x = -1) → (∫ x, |w x|) < (∫ x, w x * g x) + ε`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
