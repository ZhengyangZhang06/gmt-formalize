# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_weak_limit-a1.chart_transfer-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-59592c490f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_weak_limit-a1`
- Child key: `chart_transfer`
- Declaration: `Submission.dor_lmbsf_pwl_chart_pairing_transfer`
- Exact Lean type: `∀ (P d : ℕ) (V C Y : Set (Euclid d)) (ψ : Euclid d → Euclid P) (w : Euclid P → ℝ) (W : Euclid P → Euclid P) (c' : ℝ), IsOpen V → ContDiffOn ℝ 1 ψ V → InjOn ψ V → (∀ y ∈ V, Injective (fderiv ℝ ψ y)) → IsCompact C → C ⊆ V → MeasurableSet Y → Y ⊆ C → IntegrableOn w (ψ '' Y) μHE[d] → Measurable W → (∀ x, ‖W x‖ ≤ c') → (∀ᵐ x ∂(μHE[d].restrict (ψ '' Y)), ∀ y ∈ Y, ψ y = x → W x ∈ LinearMap.range (fderiv ℝ ψ y : Euclid d →ₗ[ℝ] Euclid P)) → ∃ Φ : Euclid d → Euclid d, Integrable Φ ∧ (∀ y, y ∉ Y → Φ y = 0) ∧ ∀ (β : Euclid P → (Euclid P →L[ℝ] ℝ)) (α : Euclid d → (Euclid d →L[ℝ] ℝ)), (∀ y ∈ Y, (β (ψ y)).comp (fderiv ℝ ψ y) = α y) → ∫ x in ψ '' Y, w x * β x (W x) ∂μHE[d] = ∫ y, α y (Φ y)`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_weak_limit-a1.left_inverse-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
