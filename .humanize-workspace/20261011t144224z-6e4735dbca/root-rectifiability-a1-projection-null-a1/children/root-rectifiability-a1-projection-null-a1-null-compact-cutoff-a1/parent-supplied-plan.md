# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rectifiability-a1.projection_null-a1.null_compact_cutoff-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-projection-null-a1-null-compact-cutoff-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rectifiability-a1.projection_null-a1`
- Child key: `null_compact_cutoff`
- Declaration: `Submission.rpn_null_compact_cutoff`
- Exact Lean type: `∀ (N : ℕ) (F : Set (Eucl N)), IsCompact F → (volume : Measure (Eucl N)) F = 0 → ∀ δ : ℝ, 0 < δ → ∃ b : Eucl N → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b ∧ HasCompactSupport b ∧ (∀ y, 0 ≤ b y ∧ b y ≤ 1) ∧ (∀ y ∈ F, b y = 1) ∧ ((volume : Measure (Eucl N)) (tsupport b)).toReal ≤ δ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
