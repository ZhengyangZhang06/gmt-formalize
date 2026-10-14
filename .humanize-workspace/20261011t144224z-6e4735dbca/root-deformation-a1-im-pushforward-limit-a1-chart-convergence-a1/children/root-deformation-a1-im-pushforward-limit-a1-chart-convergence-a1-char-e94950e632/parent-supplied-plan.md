# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1.chart_representation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-pushforward-limit-a1-chart-convergence-a1-char-e94950e632/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1`
- Child key: `chart_representation`
- Declaration: `Submission.deformation_ipl_cc_chart_integral_representation`
- Exact Lean type: `∀ (P Q k : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) k) (Φ : Eucl k → Eucl P) (Ω : Set (Eucl k)) (G : Set (Eucl P)), IsOpen U → IsRectifiableTriple U k M θ ξ → IsOpen Ω → ContDiff ℝ 1 Φ → (∃ K : ℝ≥0, LipschitzOnWith K Φ Ω) → (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → G ⊆ M → G ⊆ Φ '' Ω → NullMeasurableSet G (μHE[k] : Measure (Eucl P)) → IntegrableOn θ G (μHE[k] : Measure (Eucl P)) → ∃ ψ : Eucl k → ℝ, IntegrableOn ψ Ω (volume : Measure (Eucl k)) ∧ ∀ (f : Eucl P → Eucl Q) (A : Eucl P → (Eucl P →L[ℝ] Eucl Q)) (α : Eucl Q → Covector (Eucl Q) k), (∀ᵐ w ∂((volume : Measure (Eucl k)).restrict (Ω ∩ Φ ⁻¹' G)), HasFDerivAt (f ∘ Φ) ((A (Φ w)).comp (fderiv ℝ Φ w)) w) → IntegrableOn (fun x => θ x * nVectorPushforward k (A x) (ξ x) (α (f x))) G (μHE[k] : Measure (Eucl P)) → ∫ x in G, θ x * nVectorPushforward k (A x) (ξ x) (α (f x)) ∂(μHE[k] : Measure (Eucl P)) = ∫ w in Ω, ψ w * α (f (Φ w)) (fun b => fderiv ℝ (f ∘ Φ) w (EuclideanSpace.single b 1)) ∂(volume : Measure (Eucl k))`

## Sibling prerequisites

- `root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1.gram_det_lower_bound-a1`
- `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.chart_approximate_tangent-a1.fderiv_lower_bound-a1`
- `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1.chart_change_of_variables-a1`
- `root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1.signed_change_of_variables-a1`
- `root.deformation-a1.im_pushforward_limit-a1.chart_convergence-a1.chart_orientation-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
