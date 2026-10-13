# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.c1_submanifold_tangent-a1.chart_blowup_tendsto-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-ae-approx-tangent-exists-a1-c1-submani-c4fe112b7e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.c1_submanifold_tangent-a1`
- Child key: `chart_blowup_tendsto`
- Declaration: `Submission.rsod_c1tan_chart_blowUp_tendsto`
- Exact Lean type: `∀ (m N : ℕ) (V : Set (Rn m)) (φ : Rn m → EuclideanSpace ℝ (Fin N)) (J : Rn m → ℝ) (L : Rn m →L[ℝ] EuclideanSpace ℝ (Fin N)) (v₀ : Rn m) (c δ ε : ℝ) (f : EuclideanSpace ℝ (Fin N) → ℝ), IsOpen V → ContinuousOn φ V → ContinuousOn J V → HasFDerivAt φ L v₀ → 0 < c → 0 < δ → 0 < ε → closedBall v₀ δ ⊆ V → (∀ w : Rn m, ‖w‖ ≤ δ → c * ‖w‖ ≤ ‖φ (v₀ + w) - φ v₀‖) → (∀ v ∈ V, δ ≤ ‖v - v₀‖ → ε ≤ ‖φ v - φ v₀‖) → Continuous f → HasCompactSupport f → Tendsto (fun r : ℝ => ∫ u in {u : Rn m | v₀ + r • u ∈ V}, J (v₀ + r • u) * f (r⁻¹ • (φ (v₀ + r • u) - φ v₀)) ∂(μHE[m] : Measure (Rn m))) (𝓝[>] 0) (𝓝 (∫ u, J v₀ * f (L u) ∂(μHE[m] : Measure (Rn m))))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
