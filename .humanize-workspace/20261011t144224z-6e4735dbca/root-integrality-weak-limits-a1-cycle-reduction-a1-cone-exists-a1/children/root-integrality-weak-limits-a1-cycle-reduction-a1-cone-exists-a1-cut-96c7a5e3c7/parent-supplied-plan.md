# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.cycle_reduction-a1.cone_exists-a1.cutoff_radial-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-cone-exists-a1-cut-96c7a5e3c7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_exists-a1`
- Child key: `cutoff_radial`
- Declaration: `Submission.iwl_cr_ce_cutoff_radial_operator`
- Exact Lean type: `∀ (P m : ℕ) (r : ℝ), (∀ ω : DifferentialForm (Eucl P) (m + 1), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω → ∃ ψ : DifferentialForm (Eucl P) m, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ ∧ (∀ (x : Eucl P) (v : Fin m → Eucl P), ψ x v = ∫ t in (0 : ℝ)..1, t ^ m * ω (t • x) (Fin.cons x v)) ∧ ∀ (j : ℕ) (R D : ℝ), 0 ≤ D → (∀ i ≤ j, ∀ y ∈ closedBall (0 : Eucl P) R, ‖iteratedFDeriv ℝ i ω y‖ ≤ D) → ∀ x ∈ closedBall (0 : Eucl P) R, ‖iteratedFDeriv ℝ j ψ x‖ ≤ (R + j) * D) → ∃ Φ : TestFormOn (univ : Set (Eucl P)) (m + 1) →ₗ[ℝ] TestFormOn (univ : Set (Eucl P)) m, (∀ ωs : ℕ → TestFormOn (univ : Set (Eucl P)) (m + 1), TestFormOnConverges ωs 0 → TestFormOnConverges (fun l => Φ (ωs l)) 0) ∧ ∀ (ω : TestFormOn (univ : Set (Eucl P)) (m + 1)) (x : Eucl P), x ∈ ball (0 : Eucl P) r → ∀ v : Fin m → Eucl P, (Φ ω : DifferentialForm (Eucl P) m) x v = ∫ t in (0 : ℝ)..1, t ^ m * (ω : DifferentialForm (Eucl P) (m + 1)) (t • x) (Fin.cons x v)`

## Sibling prerequisites

- `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_exists-a1.cutoff_null-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
