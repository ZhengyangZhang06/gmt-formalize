# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.antipodal-a1.competitor-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-89a72ae371/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.antipodal-a1`
- Child key: `competitor`
- Declaration: `Submission.idtp_fons_odc_antipodal_competitor`
- Exact Lean type: `(∀ (P : ℕ) (ι : Type) [Fintype ι] (p v : ι → Euclid P) (I : ι → Set ℝ) (c : ι → ℤ), (∀ k, ‖v k‖ = 1) → (∀ k, IsOpen (I k)) → (∀ j k, j ≠ k → (μHE[1] : Measure (Euclid P)) (((fun t : ℝ => p j + t • v j) '' I j) ∩ closure ((fun t : ℝ => p k + t • v k) '' I k)) = 0) → ∃ (X : GeometricCurrentOn (univ : Set (Euclid P)) 1) (R : IMRep (univ : Set (Euclid P)) 1), R.Represents X ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) 1, X ω = ∑ k, (c k : ℝ) * ∫ t in I k, (ω : DifferentialForm (Euclid P) 1) (p k + t • v k) (fun _ => v k)) ∧ ∀ A : Set (Euclid P), MeasurableSet A → R.measure A = ∑ k, ENNReal.ofReal |(c k : ℝ)| * volume (I k ∩ (fun t : ℝ => p k + t • v k) ⁻¹' A)) → ∀ (P : ℕ) (F : Finset (Euclid P)), (∀ e ∈ F, ‖e‖ = 1) → ∀ (mo mi : Euclid P → ℤ) (b u : Euclid P) (ℓ : ℝ), 0 ≤ ℓ → ‖u‖ = 1 → (∀ (e : Euclid P) (s₁ s₂ t₁ t₂ : ℝ), b + s₁ • u = t₁ • e → b + s₂ • u = t₂ • e → s₁ = s₂) → ∃ X : GeometricCurrentOn (univ : Set (Euclid P)) 1, IsIntegerMultiplicity X ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) 1, X ω = ∑ e ∈ F, (mo e : ℝ) * (∫ t in Ioi (1 : ℝ), (ω : DifferentialForm (Euclid P) 1) (t • e) (fun _ => e)) + ∑ e ∈ F, (mi e : ℝ) * (∫ t in Ioo (0 : ℝ) 1, (ω : DifferentialForm (Euclid P) 1) (t • e) (fun _ => e)) + ∫ s in Ioo (0 : ℝ) ℓ, (ω : DifferentialForm (Euclid P) 1) (b + s • u) (fun _ => u)) ∧ X.massOn (ball (0 : Euclid P) 2) ≤ ENNReal.ofReal (∑ e ∈ F, |(mo e : ℝ)| + ∑ e ∈ F, |(mi e : ℝ)| + ℓ)`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.im_mass_measure-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
