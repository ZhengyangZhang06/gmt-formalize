# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_compact-a1.zero_current_sum-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-23d83beaa8/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_compact-a1`
- Child key: `zero_current_sum`
- Declaration: `Submission.cbr_cc_zero_current_finite_sum`
- Exact Lean type: `(∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → ∀ (P : ℕ) (S : GeometricCurrentOn (univ : Set (Euclid P)) 0), IsIntegerMultiplicity S → IsCompact S.support → ∃ (F : Finset (Euclid P)) (m : Euclid P → ℤ), (↑F : Set (Euclid P)) ⊆ S.support ∧ ∀ g : TestFormOn (univ : Set (Euclid P)) 0, S g = ∑ x ∈ F, (m x : ℝ) * (g : DifferentialForm (Euclid P) 0) x (fun i => i.elim0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
