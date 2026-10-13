# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.restriction_limit-a1.testform_cutoff-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-restriction-limit-a1-testform-cutoff-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.restriction_limit-a1`
- Child key: `testform_cutoff`
- Declaration: `Submission.iwl_rl_testForm_smooth_cutoff`
- Exact Lean type: `∀ (P k : ℕ) (U : Set (Eucl P)) (ω : TestFormOn U k) (C₀ C₁ : Set (Eucl P)), IsClosed C₀ → IsClosed C₁ → Disjoint C₀ C₁ → ∃ ω' : TestFormOn U k, (∃ N₀ : Set (Eucl P), IsOpen N₀ ∧ C₀ ⊆ N₀ ∧ ∀ x ∈ N₀, (ω' : DifferentialForm (Eucl P) k) x = 0) ∧ (∃ N₁ : Set (Eucl P), IsOpen N₁ ∧ C₁ ⊆ N₁ ∧ ∀ x ∈ N₁, (ω' : DifferentialForm (Eucl P) k) x = (ω : DifferentialForm (Eucl P) k) x) ∧ tsupport (ω' : DifferentialForm (Eucl P) k) ⊆ tsupport (ω : DifferentialForm (Eucl P) k) ∧ ∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) k) x - (ω' : DifferentialForm (Eucl P) k) x) ≤ covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) k) x)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
