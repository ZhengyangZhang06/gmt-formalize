# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.chart_pieces-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-5c77656dd0/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1`
- Child key: `chart_pieces`
- Declaration: `Submission.dor_lmbsf_lipschitz_chart_pieces`
- Exact Lean type: `(∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q) → ∀ (P n : ℕ) (U M : Set (Euclid P)) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → MeasurableSet M → M ⊆ U → CountablyRectifiable (n + 1) M → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n + 1] (M ∩ K) ≠ ∞) → LipschitzWith L f → ∃ (V C Y : ℕ → Set (Euclid (n + 1))) (ψ : ℕ → Euclid (n + 1) → Euclid P) (F : ℕ → Euclid (n + 1) → ℝ) (g : Euclid P → Euclid P), (∀ j, IsOpen (V j) ∧ ContDiffOn ℝ 1 (ψ j) (V j) ∧ InjOn (ψ j) (V j) ∧ (∀ y ∈ V j, Injective (fderiv ℝ (ψ j) y)) ∧ ψ j '' V j ⊆ U) ∧ (∀ j, IsCompact (C j) ∧ C j ⊆ V j ∧ MeasurableSet (Y j) ∧ Y j ⊆ C j ∧ ContDiff ℝ 1 (F j)) ∧ (∀ j, ψ j '' Y j ⊆ M) ∧ Pairwise (fun i j => Disjoint (ψ i '' Y i) (ψ j '' Y j)) ∧ μHE[n + 1] (M \ ⋃ j, ψ j '' Y j) = 0 ∧ (∀ j, ∀ y ∈ Y j, f (ψ j y) = F j y ∧ HasApproximateTangentSpaceAt (n + 1) M (ψ j y) (LinearMap.range (fderiv ℝ (ψ j) y : Euclid (n + 1) →ₗ[ℝ] Euclid P))) ∧ Measurable g ∧ (∀ x, ‖g x‖ ≤ L) ∧ (∀ x, (∀ j, x ∉ ψ j '' Y j) → g x = 0) ∧ ∀ j, ∀ y ∈ Y j, g (ψ j y) ∈ LinearMap.range (fderiv ℝ (ψ j) y : Euclid (n + 1) →ₗ[ℝ] Euclid P) ∧ ∀ e : Euclid (n + 1), inner ℝ (g (ψ j y)) (fderiv ℝ (ψ j) y e) = fderiv ℝ (F j) y e`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.c1_approx-a1`
- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.c1_cover-a1`
- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.image_tangent-a1`
- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.density_directions-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
