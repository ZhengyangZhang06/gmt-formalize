# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.area_formula-a1.chart_piece_formula-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-area-formula-a1-chart-piece-formula-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.area_formula-a1`
- Child key: `chart_piece_formula`
- Declaration: `Submission.areaFormula_on_chart_piece`
- Exact Lean type: `∀ (n N p : ℕ) (ψ : Rn n → Rn N) (f : Rn N → Rn p) (D : Set (Rn n)) (K C : ℝ≥0) (J : Rn N → ℝ) (S : Set (Rn N)) (h : Rn N → ℝ≥0∞), IsCompact D → (∀ u ∈ D, DifferentiableAt ℝ ψ u) → (∀ u ∈ D, Function.Injective (fderiv ℝ ψ u)) → LipschitzOnWith K ψ D → (∀ u ∈ D, ∀ v ∈ D, dist u v ≤ (C : ℝ) * dist (ψ u) (ψ v)) → LipschitzOnWith K (f ∘ ψ) D → S ⊆ ψ '' D → NullMeasurableSet S μHE[n] → (∀ᵐ u ∂(volume : Measure (Rn n)), u ∈ D → ψ u ∈ S → DifferentiableAt ℝ (f ∘ ψ) u ∧ J (ψ u) * (fderiv ℝ ψ u).toLinearMap.normDet = (fderiv ℝ (f ∘ ψ) u).toLinearMap.normDet) → AEMeasurable h ((μHE[n] : Measure (Rn N)).restrict S) → (∫⁻ x in S, h x * ENNReal.ofReal (J x) ∂μHE[n] = ∫⁻ y, ∑' x : ↥(S ∩ f ⁻¹' {y}), h x ∂μHE[n]) ∧ AEMeasurable (fun y ↦ ∑' x : ↥(S ∩ f ⁻¹' {y}), h x) (μHE[n] : Measure (Rn p))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
