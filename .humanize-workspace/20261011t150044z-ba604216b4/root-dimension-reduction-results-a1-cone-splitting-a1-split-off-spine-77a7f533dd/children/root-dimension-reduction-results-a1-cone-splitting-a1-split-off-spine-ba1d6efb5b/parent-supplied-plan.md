# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.cone_filling_subspace-a1.cone_current-a1.cutoff_homotopy-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-ba1d6efb5b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.cone_filling_subspace-a1.cone_current-a1`
- Child key: `cutoff_homotopy`
- Declaration: `Submission.dimred_cs_sos_cfs_cc_cutoff_homotopy`
- Exact Lean type: `∀ (P q : ℕ) (ρ : ℝ), (∀ β : DifferentialForm (Euclid P) (q + 1), ContDiff ℝ (⊤ : ℕ∞) β → ContDiff ℝ (⊤ : ℕ∞) (fun x : Euclid P => ∫ t in (0 : ℝ)..1, t ^ q • (β (t • x)).curryLeft x) ∧ ∀ x : Euclid P, exteriorDerivative (fun y : Euclid P => ∫ t in (0 : ℝ)..1, t ^ q • (β (t • y)).curryLeft y) x + (∫ t in (0 : ℝ)..1, t ^ (q + 1) • (exteriorDerivative β (t • x)).curryLeft x) = β x) → ∀ γ : TestFormOn (univ : Set (Euclid P)) (q + 1), ∃ ψ : TestFormOn (univ : Set (Euclid P)) q, ∀ x : Euclid P, ‖x‖ < ρ → (∫ t in (0 : ℝ)..1, t ^ (q + 1) • (exteriorDerivative (γ : DifferentialForm (Euclid P) (q + 1)) (t • x)).curryLeft x) = (γ : DifferentialForm (Euclid P) (q + 1)) x - exteriorDerivative (ψ : DifferentialForm (Euclid P) q) x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
