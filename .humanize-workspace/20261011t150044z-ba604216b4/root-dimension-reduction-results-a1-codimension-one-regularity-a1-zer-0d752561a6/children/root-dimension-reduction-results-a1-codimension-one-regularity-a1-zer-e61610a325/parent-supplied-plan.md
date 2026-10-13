# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_blowup_limit-a1.graph_representation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-e61610a325/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.graph_blowup_limit-a1`
- Child key: `graph_representation`
- Declaration: `Submission.codim1_zsl_gbl_blowUp_graph_representation`
- Exact Lean type: `∀ (n k : ℕ) (U N E : Set (Euclid (n + 1 + k))) (ξN : Euclid (n + 1 + k) → MultiVector (n + 1 + k) (n + 1)) (T : GeometricCurrentOn U n) (x y : Euclid (n + 1 + k)) (lam : ℝ) (hlam : 0 < lam) (ι : Euclid (n + 1) →ₗᵢ[ℝ] Euclid (n + 1 + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + 1 + k)) (u : Euclid (n + 1) → Euclid k) (δ₁ δ₂ : ℝ) (s : Euclid (n + 1)) (t : Euclid k), MeasurableSet E → E ⊆ N → IsBoundaryOfRegion (blowUp T y lam hlam.ne') (dilation y lam '' E) (fun z => ξN (y + lam • z)) → (∀ (g : Euclid (n + 1) → Euclid k) (D A : Set (Euclid (n + 1))) (f : Euclid (n + 1 + k) → ℝ), IsOpen D → ContDiffOn ℝ 1 g D → MeasurableSet A → A ⊆ D → ∫ z in (fun w => ι w + ι' (g w)) '' A, f z ∂μHE[n + 1] = ∫ w in A, Real.sqrt (((fderiv ℝ (fun w => ι w + ι' (g w)) w).adjoint ∘L fderiv ℝ (fun w => ι w + ι' (g w)) w).det) * f (ι w + ι' (g w))) → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ z : Euclid (n + 1 + k), ∃ v w, z = ι v + ι' w) → ContDiffOn ℝ 1 u (ball 0 δ₁) → N ∩ {z | ∃ v ∈ ball (0 : Euclid (n + 1)) δ₁, ∃ w ∈ ball (0 : Euclid k) δ₂, z = x + ι v + ι' w} = (fun v => x + ι v + ι' (u v)) '' ball (0 : Euclid (n + 1)) δ₁ → (∀ v ∈ ball (0 : Euclid (n + 1)) δ₁, ∀ α : Covector (Euclid (n + 1 + k)) (n + 1), α (fun j => fderiv ℝ (fun v => x + ι v + ι' (u v)) v (EuclideanSpace.single j (1 : ℝ))) = Real.sqrt (((fderiv ℝ (fun v => x + ι v + ι' (u v)) v).adjoint ∘L fderiv ℝ (fun v => x + ι v + ι' (u v)) v).det) * ξN (x + ι v + ι' (u v)) α) → y = x + ι s + ι' t → MeasurableSet {w : Euclid (n + 1) | s + lam • w ∈ ball (0 : Euclid (n + 1)) δ₁ ∧ x + ι (s + lam • w) + ι' (u (s + lam • w)) ∈ E} ∧ ∀ R : ℝ, ‖s‖ + lam * R < δ₁ → ‖t‖ + lam * R < δ₂ → ball y (lam * R) ⊆ U → ∀ ω : TestFormOn (univ : Set (Euclid (n + 1 + k))) n, tsupport (ω : DifferentialForm (Euclid (n + 1 + k)) n) ⊆ ball 0 R → currentEval (blowUp T y lam hlam.ne') (ω : DifferentialForm (Euclid (n + 1 + k)) n) = ∫ w in {w : Euclid (n + 1) | s + lam • w ∈ ball (0 : Euclid (n + 1)) δ₁ ∧ x + ι (s + lam • w) + ι' (u (s + lam • w)) ∈ E} ∩ ball 0 R, exteriorDerivative (ω : DifferentialForm (Euclid (n + 1 + k)) n) (ι w + ι' (lam⁻¹ • (u (s + lam • w) - t))) (fun j => fderiv ℝ (fun w => ι w + ι' (lam⁻¹ • (u (s + lam • w) - t))) w (EuclideanSpace.single j (1 : ℝ)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
