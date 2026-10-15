# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.total_boundedness-a1.translation_estimate-a1.translation_dual-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1-translation-estimate-a1-tr-ceedffce88/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1.total_boundedness-a1.translation_estimate-a1`
- Child key: `translation_dual`
- Declaration: `Submission.fiw_tb_te_translation_dual`
- Exact Lean type: `∀ (n : ℕ) (u : Eucl n → ℝ) (h : Eucl n) (B : ℝ), Integrable u → (∀ φ : Eucl n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ → (∀ x, |φ x| ≤ 1) → |∫ x, u x * fderiv ℝ φ x h| ≤ B) → ∀ g : Eucl n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g → HasCompactSupport g → (∀ x, |g x| ≤ 1) → |∫ x, (u (x + h) - u x) * g x| ≤ B`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
