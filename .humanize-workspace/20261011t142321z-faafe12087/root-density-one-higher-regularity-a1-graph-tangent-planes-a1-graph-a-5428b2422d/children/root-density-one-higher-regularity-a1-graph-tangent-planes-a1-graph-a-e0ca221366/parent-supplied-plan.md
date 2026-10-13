# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.graph_tangent_planes-a1.graph_approx_tangent-a1.bilip_integral_tendsto-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-graph-tangent-planes-a1-graph-a-e0ca221366/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.graph_tangent_planes-a1.graph_approx_tangent-a1`
- Child key: `bilip_integral_tendsto`
- Declaration: `Submission.dohr_tp_gat_bilip_setIntegral_tendsto`
- Exact Lean type: `∀ (n ℓ : ℕ) (K : Set (Rn n)) (pr : Amb n ℓ →L[ℝ] Rn n) (L : Rn n →L[ℝ] Amb n ℓ) (F : ℝ → Rn n → Amb n ℓ) (φ : Amb n ℓ → ℝ), IsCompact K → Continuous φ → HasCompactSupport φ → (∀ v, pr (L v) = v) → (∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ v ∈ K, pr (F t v) = v) → (∀ ε : ℝ, 0 < ε → ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ v ∈ K, ∀ v' ∈ K, ‖F t v - F t v' - L (v - v')‖ ≤ ε * ‖v - v'‖) → (∀ ε : ℝ, 0 < ε → ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ v ∈ K, ‖F t v - L v‖ ≤ ε) → Tendsto (fun t : ℝ => ∫ w in F t '' K, φ w ∂(μHE[n] : Measure (Amb n ℓ))) (𝓝[>] 0) (𝓝 (∫ w in L '' K, φ w ∂(μHE[n] : Measure (Amb n ℓ))))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
