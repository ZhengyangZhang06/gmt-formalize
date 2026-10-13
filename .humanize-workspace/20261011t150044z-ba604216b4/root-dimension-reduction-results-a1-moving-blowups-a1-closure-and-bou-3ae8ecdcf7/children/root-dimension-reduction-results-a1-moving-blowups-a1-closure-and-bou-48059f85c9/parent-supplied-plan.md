# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.closure_zero-a1.imrep_point_sum-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-48059f85c9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.closure_zero-a1`
- Child key: `imrep_point_sum`
- Declaration: `Submission.dmcbrz_imrep_zero_local_point_sum`
- Exact Lean type: `∀ (P : ℕ) (U B : Set (Euclid P)) (R : IMRep U 0) (S : GeometricCurrentOn U 0), R.Represents S → CompactlyContained B U → ∃ (N : ℕ) (w : ℕ → ℤ) (x : ℕ → Euclid P), (∀ l < N, x l ∈ B) ∧ (∀ l < N, w l ≠ 0) ∧ (∑ l ∈ Finset.range N, ((w l).natAbs : ℝ≥0∞)) ≤ R.measure B ∧ ∀ ω : TestFormOn U 0, tsupport (ω : DifferentialForm (Euclid P) 0) ⊆ B → S ω = ∑ l ∈ Finset.range N, (w l : ℝ) * (ω : DifferentialForm (Euclid P) 0) (x l) (fun i => i.elim0)`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_zero-a1.count_integral-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
