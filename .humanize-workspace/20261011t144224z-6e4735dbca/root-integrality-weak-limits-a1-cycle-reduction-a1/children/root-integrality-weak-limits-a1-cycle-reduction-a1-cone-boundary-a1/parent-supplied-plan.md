# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.cycle_reduction-a1.cone_boundary-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-boundary-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.cycle_reduction-a1`
- Child key: `cone_boundary`
- Declaration: `Submission.iwl_cr_cone_boundary`
- Exact Lean type: `∀ (P m : ℕ) (R : ℝ) (Y C : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)), Y.support ⊆ closedBall 0 R → (∀ (ω : TestFormOn (univ : Set (Eucl P)) (m + 1)) (ψ : TestFormOn (univ : Set (Eucl P)) m), (∃ N : Set (Eucl P), IsOpen N ∧ Y.boundary.support ⊆ N ∧ ∀ x ∈ N, ∀ v : Fin m → Eucl P, (ψ : DifferentialForm (Eucl P) m) x v = ∫ t in (0 : ℝ)..1, t ^ m * (ω : DifferentialForm (Eucl P) (m + 1)) (t • x) (Fin.cons x v)) → C ω = Y.boundary ψ) → C.boundary = Y.boundary`

## Sibling prerequisites

- `root.isoperimetric-a1.vanish_off_support-a1`
- `root.integrality_weak_limits-a1.cycle_reduction-a1.radial_operator-a1`
- `root.integrality_weak_limits-a1.cycle_reduction-a1.radial_homotopy-a1`
- `root.integrality_weak_limits-a1.cycle_reduction-a1.support_lemmas-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
