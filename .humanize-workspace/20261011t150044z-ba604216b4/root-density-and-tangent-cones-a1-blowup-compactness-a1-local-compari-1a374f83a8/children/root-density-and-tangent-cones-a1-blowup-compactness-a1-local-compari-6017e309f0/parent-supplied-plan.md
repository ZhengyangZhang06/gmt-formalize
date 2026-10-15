# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.lipschitz_leibniz-a1.weak_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-6017e309f0/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.lipschitz_leibniz-a1`
- Child key: `weak_limit`
- Declaration: `Submission.dtc_bc_lc_sl_ll_weak_limit`
- Exact Lean type: `∀ (P n : ℕ) (M : Set (Euclid P)) (h : Euclid P → ℝ) (K : NNReal) (H : Euclid P → Euclid P) (ψ : ℕ → Euclid (n + 1) → Euclid P) (V Y : ℕ → Set (Euclid (n + 1))) (F : ℕ → Euclid (n + 1) → ℝ) (hs : ℕ → Euclid P → ℝ) (w : Euclid P → Euclid P), MeasurableSet M → (∀ C : Set (Euclid P), IsCompact C → μHE[n + 1] (M ∩ C) ≠ ∞) → LipschitzWith K h → Measurable H → (∀ x, ‖H x‖ ≤ K) → (∀ᵐ x ∂(μHE[n + 1].restrict M), HasApproximateTangentSpaceAt (n + 1) M x (approxTangentPlane (n + 1) M x) ∧ H x ∈ approxTangentPlane (n + 1) M x ∧ ∀ ε : ℝ, 0 < ε → Tendsto (fun r : ℝ => μHE[n + 1] (M ∩ ball x r ∩ {y | ε * ‖y - x‖ < |h y - h x - inner ℝ (H x) (y - x)|}) / ENNReal.ofReal (r ^ (n + 1))) (𝓝[>] 0) (𝓝 0)) → (∀ j, IsOpen (V j) ∧ ContDiff ℝ 1 (ψ j) ∧ InjOn (ψ j) (V j) ∧ (∀ y ∈ V j, Injective (fderiv ℝ (ψ j) y)) ∧ ContDiff ℝ 1 (F j) ∧ MeasurableSet (Y j) ∧ IsCompact (closure (Y j)) ∧ closure (Y j) ⊆ V j ∧ ψ j '' Y j ⊆ M ∧ (∀ y ∈ Y j, h (ψ j y) = F j y) ∧ ∀ y ∈ Y j, HasApproximateTangentSpaceAt (n + 1) M (ψ j y) (LinearMap.range (fderiv ℝ (ψ j) y : Euclid (n + 1) →ₗ[ℝ] Euclid P))) → Pairwise (fun i j => Disjoint (ψ i '' Y i) (ψ j '' Y j)) → μHE[n + 1] (M \ ⋃ j, ψ j '' Y j) = 0 → (∀ k, ContDiff ℝ 1 (hs k)) → (∀ k x, ‖fderiv ℝ (hs k) x‖ ≤ K) → TendstoUniformly hs h atTop → IntegrableOn w M μHE[n + 1] → (∀ᵐ x ∂(μHE[n + 1].restrict M), w x ∈ approxTangentPlane (n + 1) M x) → Tendsto (fun k => ∫ x in M, fderiv ℝ (hs k) x (w x) ∂μHE[n + 1]) atTop (𝓝 (∫ x in M, inner ℝ (H x) (w x) ∂μHE[n + 1]))`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.lipschitz_leibniz-a1.piece_gradient-a1`
- `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.slicing-a1.lipschitz_leibniz-a1.piece_weak_limit-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
