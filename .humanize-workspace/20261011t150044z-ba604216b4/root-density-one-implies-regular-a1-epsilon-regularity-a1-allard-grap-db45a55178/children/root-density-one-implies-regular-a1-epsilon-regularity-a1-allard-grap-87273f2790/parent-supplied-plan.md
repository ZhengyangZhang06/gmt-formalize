# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.graph_c1-a1.slope_campanato-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-87273f2790/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.graph_c1-a1`
- Child key: `slope_campanato`
- Declaration: `Submission.dorag_gc_graph_slope_campanato`
- Exact Lean type: `∀ (n k : ℕ) (U W : Set (Euclid (n + k))) (R : IMRep U n) (κ : ℝ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (f : Euclid n → Euclid k) (z : Euclid (n + k)) (a s₀ K : ℝ), IsOpen W → W ⊆ U → AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → (∀ y ∈ R.measure.support, ∀ t : ℝ, 0 < t → closedBall y t ⊆ W → unitBallVolume n ≤ ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * R.measure (closedBall y t)) → μHE[n] ((R.measure.support ∩ W) \ R.carrier) = 0 → (∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ W)), ∀ v : Euclid n, x = z + ι v + ι' (f v) → DifferentiableAt ℝ f v ∧ approxTangentPlane n R.carrier x = LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ (fderiv ℝ f v).toLinearMap)) → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ v w, ‖f v - f w‖ ≤ 1 / 4 * ‖v - w‖) → f 0 = 0 → 0 < a → 0 < s₀ → closedBall z a ⊆ W → R.measure.support ∩ closedBall z a = range (fun v => z + ι v + ι' (f v)) ∩ closedBall z a → (∀ ξ ∈ R.measure.support ∩ closedBall z a, ∃ S : Submodule ℝ (Euclid (n + k)), Module.finrank ℝ S = n ∧ ∀ s : ℝ, 0 < s → s ≤ s₀ → ∫⁻ x in closedBall ξ s, ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure ≤ ENNReal.ofReal (K * s ^ (n + 1))) → ∃ C s₁ : ℝ, 0 ≤ C ∧ 0 < s₁ ∧ ∀ᵐ v ∂volume, v ∈ ball (0 : Euclid n) (a / 2) → DifferentiableAt ℝ f v ∧ ∀ s : ℝ, 0 < s → s ≤ s₁ → ∫⁻ w in ball v s, ENNReal.ofReal (∑ i : Fin n, ‖(fderiv ℝ f w - fderiv ℝ f v) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ≤ ENNReal.ofReal (C * s ^ (n + 1))`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.graph_c1-a1.graph_tangent_ae-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.graph_c1-a1.graph_pushforward-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.graph_c1-a1.graph_projection-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
