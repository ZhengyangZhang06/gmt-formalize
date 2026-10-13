# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.allard_lemma-a1.cylinder_monotonicity-a1.radial_cutoff-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1-cylinder-monotonicity-a1-a20306f1bb/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.allard_lemma-a1.cylinder_monotonicity-a1`
- Child key: `radial_cutoff`
- Declaration: `Submission.intcpt_allard_cm_radial_cutoff`
- Exact Lean type: `∀ A : ℝ, 1 < A → ∃ φ : ℝ → ℝ, ContDiff ℝ 1 φ ∧ Antitone φ ∧ (∀ s, 0 ≤ φ s ∧ φ s ≤ 1) ∧ (∀ s, s ≤ 1 → φ s = 1) ∧ (∀ s, A ^ 2 ≤ s → φ s = 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
