# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.cone_filling_subspace-a1.cone_current-a1.cutoff_cone_operator-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-d088f14f22/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.cone_filling_subspace-a1.cone_current-a1`
- Child key: `cutoff_cone_operator`
- Declaration: `Submission.dimred_cs_sos_cfs_cc_cutoff_cone_operator`
- Exact Lean type: `∀ (P q : ℕ) (ρ : ℝ), 0 < ρ → (∀ β : DifferentialForm (Euclid P) (q + 1 + 1), ContDiff ℝ (⊤ : ℕ∞) β → ContDiff ℝ (⊤ : ℕ∞) (fun x : Euclid P => ∫ t in (0 : ℝ)..1, t ^ (q + 1) • (β (t • x)).curryLeft x)) → ∃ Φ : TestFormOn (univ : Set (Euclid P)) (q + 1 + 1) →ₗ[ℝ] TestFormOn (univ : Set (Euclid P)) (q + 1), (∀ (ω : TestFormOn (univ : Set (Euclid P)) (q + 1 + 1)) (x : Euclid P), ‖x‖ < ρ → (Φ ω : DifferentialForm (Euclid P) (q + 1)) x = ∫ t in (0 : ℝ)..1, t ^ (q + 1) • ((ω : DifferentialForm (Euclid P) (q + 1 + 1)) (t • x)).curryLeft x) ∧ ∀ (ω : TestFormOn (univ : Set (Euclid P)) (q + 1 + 1)) (b : ℝ), (∀ y, ‖(ω : DifferentialForm (Euclid P) (q + 1 + 1)) y‖ ≤ b) → ∀ x, ‖(Φ ω : DifferentialForm (Euclid P) (q + 1)) x‖ ≤ (ρ + 1) * b`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
