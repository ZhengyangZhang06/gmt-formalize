# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.fibre_area-a1.area_formula_prod-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-52a49d468c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_sector_endpoint_density-a1.fibre_area-a1`
- Child key: `area_formula_prod`
- Declaration: `Submission.idtp_cse_fa_area_formula_prod`
- Exact Lean type: `∀ (P : ℕ) (M Z : Set (Euclid P)) (F : Euclid P → ℝ × ℝ) (h : Euclid P → ℝ≥0∞), MeasurableSet M → CountablyRectifiable 2 M → (∀ K : Set (Euclid P), IsCompact K → μHE[2] (M ∩ K) ≠ ∞) → IsOpen Z → ContDiffOn ℝ 1 F Z → AEMeasurable h (μHE[2].restrict M) → AEMeasurable (fun p : ℝ × ℝ => ∑' x : ↥(M ∩ Z ∩ F ⁻¹' {p}), h x) volume ∧ ∫⁻ p : ℝ × ℝ, (∑' x : ↥(M ∩ Z ∩ F ⁻¹' {p}), h x) = ∫⁻ x in M ∩ Z, ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (Module.finrank ℝ (approxTangentPlane 2 M x)) => (fderiv ℝ F x (stdOrthonormalBasis ℝ (approxTangentPlane 2 M x) i)).1 * (fderiv ℝ F x (stdOrthonormalBasis ℝ (approxTangentPlane 2 M x) j)).1 + (fderiv ℝ F x (stdOrthonormalBasis ℝ (approxTangentPlane 2 M x) i)).2 * (fderiv ℝ F x (stdOrthonormalBasis ℝ (approxTangentPlane 2 M x) j)).2))) * h x ∂μHE[2]`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
