# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_succ-a1.cutoff_extension-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-c14d29cb77/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_succ-a1`
- Child key: `cutoff_extension`
- Declaration: `Submission.cbrcs_cutoff_extension`
- Exact Lean type: `∀ (P m : ℕ) (U K : Set (Euclid P)), IsOpen U → IsCompact K → K ⊆ U → ∃ E : GeometricCurrentOn U (m + 1) → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), (∀ (X : GeometricCurrentOn U (m + 1)) (ω : TestFormOn U (m + 1)), tsupport (ω : DifferentialForm (Euclid P) (m + 1)) ⊆ K → E X (testFormOnInclusion (subset_univ U) (m + 1) ω) = X ω) ∧ (∀ (Xs : ℕ → GeometricCurrentOn U (m + 1)) (X : GeometricCurrentOn U (m + 1)), WeaklyConvergesOn Xs X → WeaklyConvergesOn (fun j => E (Xs j)) (E X)) ∧ (∀ X : GeometricCurrentOn U (m + 1), (E X).mass ≤ X.mass) ∧ (∀ X : GeometricCurrentOn U (m + 1), (∀ ω : TestFormOn U (m + 1), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 1))) K → X ω = 0) → (E X).support ⊆ K ∧ (E X).boundary.mass ≤ X.boundary.mass) ∧ (∀ (X : GeometricCurrentOn U (m + 1)) (R : IMRep U (m + 1)), R.Represents X → R.carrier ⊆ K → IsIntegerMultiplicity (E X))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
