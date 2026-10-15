# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.carrier_area_formula-a1.piece_area_formula-a1.fiber_side-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-7aaee2fdb9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.carrier_area_formula-a1.piece_area_formula-a1`
- Child key: `fiber_side`
- Declaration: `Submission.idtp_caf_paf_fiber_side`
- Exact Lean type: `∀ (P n : ℕ) (g : Euclid n → Euclid P) (A : Set (Euclid n)) (F : Euclid P → Euclid n) (Φ : Euclid n → Euclid n) (LΦ : NNReal) (h : Euclid P → ℝ≥0∞), Continuous g → MeasurableSet A → InjOn g A → LipschitzWith LΦ Φ → (∀ a ∈ A, F (g a) = Φ a) → Measurable h → AEMeasurable (fun y : Euclid n => ∑' x : ↥(g '' A ∩ F ⁻¹' {y}), h x) volume ∧ ∫⁻ y, (∑' x : ↥(g '' A ∩ F ⁻¹' {y}), h x) ∂volume = ∫⁻ a in A, ENNReal.ofReal |LinearMap.det (fderiv ℝ Φ a : Euclid n →ₗ[ℝ] Euclid n)| * h (g a) ∂volume`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
