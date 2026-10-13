# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.skeleton_deformation-a1.support_calculus-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-ske-fc82e8a21d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.skeleton_deformation-a1`
- Child key: `support_calculus`
- Declaration: `Submission.cmcsd_support_calculus`
- Exact Lean type: `∀ (P n : ℕ), (∀ (E : Set (Euclid P)) (X : GeometricCurrentOn (univ : Set (Euclid P)) n), IsClosed E → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) E → X ω = 0) → X.support ⊆ E) ∧ (∀ X : GeometricCurrentOn (univ : Set (Euclid P)) n, IsClosed X.support) ∧ (∀ A B : GeometricCurrentOn (univ : Set (Euclid P)) n, (A - B).support ⊆ A.support ∪ B.support) ∧ (0 : GeometricCurrentOn (univ : Set (Euclid P)) n).support = ∅ ∧ (∀ A : GeometricCurrentOn (univ : Set (Euclid P)) (n + 1), A.boundary.support ⊆ A.support)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
