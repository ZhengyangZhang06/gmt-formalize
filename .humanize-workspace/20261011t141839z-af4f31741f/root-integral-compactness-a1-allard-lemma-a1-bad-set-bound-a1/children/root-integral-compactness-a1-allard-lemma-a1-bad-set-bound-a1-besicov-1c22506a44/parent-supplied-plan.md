# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.allard_lemma-a1.bad_set_bound-a1.besicovitch_cover-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1-bad-set-bound-a1-besicov-1c22506a44/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.allard_lemma-a1.bad_set_bound-a1`
- Child key: `besicovitch_cover`
- Declaration: `Submission.intcpt_allard_bsb_besicovitch_cover`
- Exact Lean type: `∀ N : ℕ, ∃ C : ℕ, ∀ (μ ν : Measure (Euclidean N)) (A O : Set (Euclidean N)) (R : ℝ) (t : ℝ≥0∞), (∀ x ∈ A, ∃ σ : ℝ, 0 < σ ∧ σ ≤ R ∧ closedBall x σ ⊆ O ∧ μ (closedBall x σ) ≤ t * ν (closedBall x σ)) → μ A ≤ (C : ℝ≥0∞) * t * ν O`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
