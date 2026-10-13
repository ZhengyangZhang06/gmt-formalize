# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.planar_constancy-a1.plane_test_extension-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-e2b61fb9ff/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.planar_constancy-a1`
- Child key: `plane_test_extension`
- Declaration: `Submission.idtp_pc_plane_test_extension`
- Exact Lean type: `∀ (P n : ℕ) (V : Set (Euclid P)) (τ : Fin n → Euclid P) (ψ : Euclid n → ℝ), IsOpen V → Orthonormal ℝ τ → ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ {s : Euclid n | ∑ i, s i • τ i ∈ V} → ∃ f : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ tsupport f ⊆ V ∧ ∀ s : Euclid n, f (∑ i, s i • τ i) = ψ s ∧ ∀ j : Fin n, fderiv ℝ f (∑ i, s i • τ i) (τ j) = fderiv ℝ ψ s (EuclideanSpace.single j (1 : ℝ))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
