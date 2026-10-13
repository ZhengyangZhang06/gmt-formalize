# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.cycle_reduction-a1.cone_estimates-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-estimates-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.cycle_reduction-a1`
- Child key: `cone_estimates`
- Declaration: `Submission.iwl_cr_cone_estimates`
- Exact Lean type: `∀ (P m : ℕ), ∃ c : ℝ, 0 ≤ c ∧ ∀ R : ℝ, 0 ≤ R → (∀ (X : GeometricCurrentOn (univ : Set (Eucl P)) m) (C : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)), X.support ⊆ closedBall 0 R → (∀ (ω : TestFormOn (univ : Set (Eucl P)) (m + 1)) (ψ : TestFormOn (univ : Set (Eucl P)) m), (∃ N : Set (Eucl P), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, ∀ v : Fin m → Eucl P, (ψ : DifferentialForm (Eucl P) m) x v = ∫ t in (0 : ℝ)..1, t ^ m * (ω : DifferentialForm (Eucl P) (m + 1)) (t • x) (Fin.cons x v)) → C ω = X ψ) → C.support ⊆ closedBall 0 R ∧ (X.mass < ∞ → C.mass ≤ ENNReal.ofReal (c * R) * X.mass)) ∧ (∀ (Xj : ℕ → GeometricCurrentOn (univ : Set (Eucl P)) m) (X : GeometricCurrentOn (univ : Set (Eucl P)) m) (Cj : ℕ → GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)) (C : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)), (∀ j, (Xj j).support ⊆ closedBall 0 R) → X.support ⊆ closedBall 0 R → (∀ j, (∀ (ω : TestFormOn (univ : Set (Eucl P)) (m + 1)) (ψ : TestFormOn (univ : Set (Eucl P)) m), (∃ N : Set (Eucl P), IsOpen N ∧ (Xj j).support ⊆ N ∧ ∀ x ∈ N, ∀ v : Fin m → Eucl P, (ψ : DifferentialForm (Eucl P) m) x v = ∫ t in (0 : ℝ)..1, t ^ m * (ω : DifferentialForm (Eucl P) (m + 1)) (t • x) (Fin.cons x v)) → (Cj j) ω = (Xj j) ψ)) → (∀ (ω : TestFormOn (univ : Set (Eucl P)) (m + 1)) (ψ : TestFormOn (univ : Set (Eucl P)) m), (∃ N : Set (Eucl P), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, ∀ v : Fin m → Eucl P, (ψ : DifferentialForm (Eucl P) m) x v = ∫ t in (0 : ℝ)..1, t ^ m * (ω : DifferentialForm (Eucl P) (m + 1)) (t • x) (Fin.cons x v)) → C ω = X ψ) → WeaklyConvergesOn Xj X → WeaklyConvergesOn Cj C)`

## Sibling prerequisites

- `root.compactness_mass_bounds-a1.mass_bound-a1`
- `root.isoperimetric-a1.covector_eval_bound-a1`
- `root.integrality_weak_limits-a1.cycle_reduction-a1.radial_operator-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
