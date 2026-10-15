# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_slice_tangent-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-f08a01d1b0/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1`
- Child key: `piece_slice_tangent`
- Declaration: `Submission.dor_lmbsf_piece_slice_approxTangent`
- Exact Lean type: `(∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q) → ∀ (P n : ℕ) (V C Y : Set (Euclid (n + 1))) (ψ : Euclid (n + 1) → Euclid P) (F : Euclid (n + 1) → ℝ) (f : Euclid P → ℝ) (G : Euclid P → Euclid P), IsOpen V → ContDiffOn ℝ 1 ψ V → InjOn ψ V → (∀ y ∈ V, Injective (fderiv ℝ ψ y)) → IsCompact C → C ⊆ V → MeasurableSet Y → Y ⊆ C → ContDiff ℝ 1 F → (∀ y ∈ Y, f (ψ y) = F y) → (∀ y ∈ Y, G (ψ y) ∈ LinearMap.range (fderiv ℝ ψ y : Euclid (n + 1) →ₗ[ℝ] Euclid P) ∧ ∀ e : Euclid (n + 1), inner ℝ (G (ψ y)) (fderiv ℝ ψ y e) = fderiv ℝ F y e) → ∀ t : ℝ, CountablyRectifiable n (ψ '' Y ∩ {x | G x ≠ 0} ∩ f ⁻¹' {t}) ∧ (μHE[n] (ψ '' Y ∩ {x | G x ≠ 0} ∩ f ⁻¹' {t}) ≠ ∞ → ∀ᵐ x ∂(μHE[n].restrict (ψ '' Y ∩ {x | G x ≠ 0} ∩ f ⁻¹' {t})), ∀ y ∈ Y, ψ y = x → HasApproximateTangentSpaceAt n (ψ '' Y ∩ {x | G x ≠ 0} ∩ f ⁻¹' {t}) x (LinearMap.range (fderiv ℝ ψ y : Euclid (n + 1) →ₗ[ℝ] Euclid P) ⊓ (ℝ ∙ G x)ᗮ))`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.image_tangent-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
