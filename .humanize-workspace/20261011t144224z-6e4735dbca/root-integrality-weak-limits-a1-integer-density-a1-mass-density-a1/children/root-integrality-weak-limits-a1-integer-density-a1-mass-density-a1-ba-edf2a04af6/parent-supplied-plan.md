# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.integer_density-a1.mass_density-a1.ball_weak_subseq-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-mass-density-a1-ba-edf2a04af6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.integer_density-a1.mass_density-a1`
- Child key: `ball_weak_subseq`
- Declaration: `Submission.ind_md_closedBall_weak_subseq`
- Exact Lean type: `∀ (P R : ℕ) (μ : ℕ → Measure (Eucl P)), (⨆ j, μ j univ) < ∞ → ∃ (χ : ℕ → ℕ) (ν : Measure (Eucl P)), StrictMono χ ∧ ν univ < ∞ ∧ ∀ F : Set (Eucl P), IsClosed F → F ⊆ closedBall 0 (R : ℝ) → limsup (fun i => μ (χ i) F) atTop ≤ ν F`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
