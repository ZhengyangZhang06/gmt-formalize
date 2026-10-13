# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.cycle_reduction-a1.support_lemmas-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-support-lemmas-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.cycle_reduction-a1`
- Child key: `support_lemmas`
- Declaration: `Submission.iwl_cr_support_lemmas`
- Exact Lean type: `(∀ (P m : ℕ) (U : Set (Eucl P)) (Z : GeometricCurrentOn U (m + 1)), Z.boundary.support ⊆ Z.support) ∧ (∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (K : Set (Eucl P)) (Zj : ℕ → GeometricCurrentOn U n) (Z : GeometricCurrentOn U n), IsClosed K → (∀ j, (Zj j).support ⊆ K) → WeaklyConvergesOn Zj Z → Z.support ⊆ K) ∧ (∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (Z₁ Z₂ Z : GeometricCurrentOn U n) (a b : ℝ), (∀ ω : TestFormOn U n, Z ω = a * Z₁ ω + b * Z₂ ω) → Z.support ⊆ Z₁.support ∪ Z₂.support)`

## Sibling prerequisites

- `root.isoperimetric-a1.vanish_off_support-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
