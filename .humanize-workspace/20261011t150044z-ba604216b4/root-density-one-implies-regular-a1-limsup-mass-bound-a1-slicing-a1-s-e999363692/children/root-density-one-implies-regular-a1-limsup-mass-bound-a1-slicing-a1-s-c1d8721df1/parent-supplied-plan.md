# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.tangential_gradient-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-c1d8721df1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1`
- Child key: `tangential_gradient`
- Declaration: `Submission.dor_lmbsf_tangential_gradient`
- Exact Lean type: `(∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q) → ∀ (P n : ℕ) (U : Set (Euclid P)) (RT : IMRep U (n + 1)) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → LipschitzWith L f → ∃ g : Euclid P → Euclid P, Measurable g ∧ (∀ x, ‖g x‖ ≤ L) ∧ (∀ᵐ x ∂(μHE[n + 1].restrict RT.carrier), g x ∈ approxTangentPlane (n + 1) RT.carrier x) ∧ (∀ φ : Euclid P → ℝ≥0∞, Measurable φ → AEMeasurable (fun t => ∫⁻ x in RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t}, φ x ∂μHE[n]) ∧ ∫⁻ t, (∫⁻ x in RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t}, φ x ∂μHE[n]) = ∫⁻ x in RT.carrier, ‖g x‖ₑ * φ x ∂μHE[n + 1]) ∧ (∀ t, CountablyRectifiable n (RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t})) ∧ (∀ t, (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t} ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict (RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t})), HasApproximateTangentSpaceAt n (RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t}) x (approxTangentPlane (n + 1) RT.carrier x ⊓ (ℝ ∙ g x)ᗮ)) ∧ (∀ (a b : ℝ), a < b → ∀ (hs : ℕ → Euclid P → ℝ) (c : ℝ), (∀ k, ContDiff ℝ 1 (hs k)) → (∀ k x, ‖fderiv ℝ (hs k) x‖ ≤ c) → TendstoUniformly hs (fun x => min 1 (max 0 ((b - f x) / (b - a)))) atTop → ∀ (W : Euclid P → Euclid P) (K : Set (Euclid P)) (c' : ℝ), Measurable W → IsCompact K → K ⊆ U → (∀ x, x ∉ K → W x = 0) → (∀ x, ‖W x‖ ≤ c') → (∀ᵐ x ∂(μHE[n + 1].restrict RT.carrier), W x ∈ approxTangentPlane (n + 1) RT.carrier x) → Tendsto (fun k => ∫ x in RT.carrier, (RT.mult x : ℝ) * fderiv ℝ (hs k) x (W x) ∂μHE[n + 1]) atTop (𝓝 (∫ x in RT.carrier ∩ {x | a < f x ∧ f x < b}, (RT.mult x : ℝ) * (-(b - a)⁻¹ * inner ℝ (g x) (W x)) ∂μHE[n + 1])))`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.chart_pieces-a1`
- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_coarea-a1`
- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_slice_tangent-a1`
- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_weak_limit-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
