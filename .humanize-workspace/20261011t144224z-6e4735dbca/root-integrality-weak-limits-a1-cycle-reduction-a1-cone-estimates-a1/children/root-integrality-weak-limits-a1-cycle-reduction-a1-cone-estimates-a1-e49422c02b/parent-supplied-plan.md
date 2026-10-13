# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.cycle_reduction-a1.cone_estimates-a1.cone_support-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-estimates-a1-e49422c02b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_estimates-a1`
- Child key: `cone_support`
- Declaration: `Submission.iwl_cr_cest_cone_support`
- Exact Lean type: `∀ (P m : ℕ) (R : ℝ) (X : GeometricCurrentOn (univ : Set (Eucl P)) m) (C : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)), X.support ⊆ closedBall 0 R → (∀ (ω : TestFormOn (univ : Set (Eucl P)) (m + 1)) (ψ : TestFormOn (univ : Set (Eucl P)) m), (∃ N : Set (Eucl P), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, ∀ v : Fin m → Eucl P, (ψ : DifferentialForm (Eucl P) m) x v = ∫ t in (0 : ℝ)..1, t ^ m * (ω : DifferentialForm (Eucl P) (m + 1)) (t • x) (Fin.cons x v)) → C ω = X ψ) → C.support ⊆ closedBall 0 R`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
