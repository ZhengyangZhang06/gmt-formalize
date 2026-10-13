# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.besicovitch_federer-a1.cone_trichotomy-a1.frame_averaging-a1.haar_to_frames-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-besicovitch-federer-a1-cone-trichotomy-a1-frame-averaging-a1-haa-04f05295fa/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.besicovitch_federer-a1.cone_trichotomy-a1.frame_averaging-a1`
- Child key: `haar_to_frames`
- Declaration: `Submission.bf_haar_null_to_frames`
- Exact Lean type: `∀ (N n : ℕ), ContinuousOn (fun v : Fin n → Rn N ↦ frameProjection v) {v | LinearIndependent ℝ v} → ∀ θ : Measure (Rn N →L[ℝ] Rn N), IsProbabilityMeasure θ → (∀ᵐ g ∂θ, ContinuousLinearMap.adjoint g * g = 1) → (∀ k : Rn N →L[ℝ] Rn N, ContinuousLinearMap.adjoint k * k = 1 → Measure.map (fun g ↦ g * k) θ = θ) → ∀ W₀ : Submodule ℝ (Rn N), finrank ℝ W₀ = n → ∀ Q : Set (Rn N →L[ℝ] Rn N), MeasurableSet Q → θ {g | g * W₀.starProjection * ContinuousLinearMap.adjoint g ∈ Q} = 0 → ForAlmostAllProjections N n (fun p ↦ p ∉ Q)`

## Sibling prerequisites

- `root.besicovitch_federer-a1.cone_trichotomy-a1.frame_averaging-a1.orthogonal_conj_projection-a1`
- `root.besicovitch_federer-a1.cone_trichotomy-a1.frame_averaging-a1.orthogonal_plane_transitive-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
