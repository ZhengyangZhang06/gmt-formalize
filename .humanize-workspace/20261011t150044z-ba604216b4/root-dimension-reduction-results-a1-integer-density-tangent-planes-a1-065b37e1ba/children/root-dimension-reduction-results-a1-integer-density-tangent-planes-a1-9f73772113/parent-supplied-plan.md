# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.carrier_area_formula-a1.piece_area_formula-a1.carrier_side-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-9f73772113/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.carrier_area_formula-a1.piece_area_formula-a1`
- Child key: `carrier_side`
- Declaration: `Submission.idtp_caf_paf_carrier_side`
- Exact Lean type: `∀ (P n : ℕ) (g : Euclid n → Euclid P) (A : Set (Euclid n)) (Lg : NNReal) (V : Set (Euclid P)) (F G : Euclid P → Euclid n) (T : Euclid P → Submodule ℝ (Euclid P)) (h : Euclid P → ℝ≥0∞), LipschitzWith Lg g → MeasurableSet A → InjOn g A → (∀ a ∈ A, DifferentiableAt ℝ g a) → IsOpen V → g '' A ⊆ V → EqOn F G V → (∀ x ∈ g '' A, DifferentiableAt ℝ F x) → (∀ᵐ a ∂(volume.restrict A), T (g a) = LinearMap.range (fderiv ℝ g a : Euclid n →ₗ[ℝ] Euclid P)) → ∫⁻ x in g '' A, ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (Module.finrank ℝ (T x)) => inner ℝ (fderiv ℝ F x (stdOrthonormalBasis ℝ (T x) i)) (fderiv ℝ F x (stdOrthonormalBasis ℝ (T x) j))))) * h x ∂μHE[n] = ∫⁻ a in A, ENNReal.ofReal |LinearMap.det (fderiv ℝ (G ∘ g) a : Euclid n →ₗ[ℝ] Euclid n)| * h (g a) ∂volume`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
