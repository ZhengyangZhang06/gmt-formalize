# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.besicovitch_federer-a1.cone_trichotomy-a1.frame_averaging-a1.pointwise_exc_null-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-besicovitch-federer-a1-cone-trichotomy-a1-frame-averaging-a1-poi-a242f472e9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.besicovitch_federer-a1.cone_trichotomy-a1.frame_averaging-a1`
- Child key: `pointwise_exc_null`
- Declaration: `Submission.bf_haar_excPointwise_null`
- Exact Lean type: `∀ (n ℓ : ℕ) (Exc : Set (Rn (n + ℓ) × (Rn (n + ℓ) →L[ℝ] Rn (n + ℓ)))) (Bad : Set (Rn (n + ℓ) × (Rn (n + ℓ) →L[ℝ] Rn (n + ℓ)) × Rn (n + ℓ))), MeasurableSet Bad → (∀ H : Submodule ℝ (Rn (n + ℓ)), finrank ℝ H = n + 1 → 0 < μHE[n] {x : Rn (n + ℓ) | x ∈ H ∧ ‖x‖ = 1} ∧ μHE[n] {x : Rn (n + ℓ) | x ∈ H ∧ ‖x‖ = 1} < ∞) → ∀ a : Rn (n + ℓ), (∀ H : Submodule ℝ (Rn (n + ℓ)), finrank ℝ H = n + 1 → μHE[n] {x | x ∈ H ∧ ‖x‖ = 1 ∧ (a, H.starProjection, x) ∈ Bad} = 0) → (∀ W : Submodule ℝ (Rn (n + ℓ)), finrank ℝ W = n → (a, W.starProjection) ∈ Exc → ∀ u : Fin ℓ → Rn (n + ℓ), Orthonormal ℝ u → (∀ j, u j ∈ Wᗮ) → ∃ j, (a, (W ⊔ Submodule.span ℝ {u j}).starProjection, u j) ∈ Bad) → ∀ θ : Measure (Rn (n + ℓ) →L[ℝ] Rn (n + ℓ)), IsProbabilityMeasure θ → (∀ᵐ g ∂θ, ContinuousLinearMap.adjoint g * g = 1) → (∀ k : Rn (n + ℓ) →L[ℝ] Rn (n + ℓ), ContinuousLinearMap.adjoint k * k = 1 → Measure.map (fun g ↦ g * k) θ = θ) → ∀ W₀ : Submodule ℝ (Rn (n + ℓ)), finrank ℝ W₀ = n → θ {g | (a, g * W₀.starProjection * ContinuousLinearMap.adjoint g) ∈ Exc} = 0`

## Sibling prerequisites

- `root.besicovitch_federer-a1.cone_trichotomy-a1.frame_averaging-a1.orthogonal_conj_projection-a1`
- `root.besicovitch_federer-a1.cone_trichotomy-a1.frame_averaging-a1.plane_direction_null-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
