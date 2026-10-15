# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.chart_pieces-a1.chart_tangent_ae-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-73d00ee3ab/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.chart_pieces-a1`
- Child key: `chart_tangent_ae`
- Declaration: `Submission.dor_lmbsf_cp_chart_tangent_ae`
- Exact Lean type: `(∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q) → ∀ (P m : ℕ) (U M : Set (Euclid P)) (C C' : Set (Euclid m)) (ψ : Euclid m → Euclid P), IsOpen U → MeasurableSet M → M ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[m] (M ∩ K) ≠ ∞) → ContDiffOn ℝ 1 ψ C' → ψ '' C' ⊆ U → IsCompact C → IsCompact C' → Convex ℝ C' → C ⊆ interior C' → (∀ y ∈ interior C', HasApproximateTangentSpaceAt m (ψ '' C') (ψ y) (LinearMap.range (fderiv ℝ ψ y : Euclid m →ₗ[ℝ] Euclid P))) → ∀ᵐ x ∂(μHE[m].restrict (M ∩ ψ '' C)), ∀ y ∈ C, ψ y = x → HasApproximateTangentSpaceAt m M x (LinearMap.range (fderiv ℝ ψ y : Euclid m →ₗ[ℝ] Euclid P))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
