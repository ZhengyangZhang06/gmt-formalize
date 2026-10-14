# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.carrier_area_formula-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-3c1713cbf6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1`
- Child key: `carrier_area_formula`
- Declaration: `Submission.idtp_carrier_area_formula`
- Exact Lean type: `∀ (P n : ℕ) (M Z : Set (Euclid P)) (F : Euclid P → Euclid n) (h : Euclid P → ℝ≥0∞), 1 ≤ n → MeasurableSet M → CountablyRectifiable n M → (∀ K : Set (Euclid P), IsCompact K → μHE[n] (M ∩ K) ≠ ∞) → IsOpen Z → ContDiffOn ℝ 1 F Z → AEMeasurable h (μHE[n].restrict M) → AEMeasurable (fun y : Euclid n => ∑' x : ↥(M ∩ Z ∩ F ⁻¹' {y}), h x) volume ∧ ∫⁻ y, (∑' x : ↥(M ∩ Z ∩ F ⁻¹' {y}), h x) ∂volume = ∫⁻ x in M ∩ Z, ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (Module.finrank ℝ (approxTangentPlane n M x)) => inner ℝ (fderiv ℝ F x (stdOrthonormalBasis ℝ (approxTangentPlane n M x) i)) (fderiv ℝ F x (stdOrthonormalBasis ℝ (approxTangentPlane n M x) j))))) * h x ∂μHE[n]`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
