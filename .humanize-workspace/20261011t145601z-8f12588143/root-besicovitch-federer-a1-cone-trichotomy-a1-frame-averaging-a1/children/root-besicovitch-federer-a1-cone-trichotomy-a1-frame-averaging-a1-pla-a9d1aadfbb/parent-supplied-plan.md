# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.besicovitch_federer-a1.cone_trichotomy-a1.frame_averaging-a1.plane_direction_null-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-besicovitch-federer-a1-cone-trichotomy-a1-frame-averaging-a1-pla-a9d1aadfbb/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.besicovitch_federer-a1.cone_trichotomy-a1.frame_averaging-a1`
- Child key: `plane_direction_null`
- Declaration: `Submission.bf_haar_planeDirection_null`
- Exact Lean type: `∀ (n N : ℕ) (Bad : Set (Rn N × (Rn N →L[ℝ] Rn N) × Rn N)), MeasurableSet Bad → ∀ a : Rn N, (∀ H : Submodule ℝ (Rn N), finrank ℝ H = n + 1 → μHE[n] {x | x ∈ H ∧ ‖x‖ = 1 ∧ (a, H.starProjection, x) ∈ Bad} = 0) → ∀ θ : Measure (Rn N →L[ℝ] Rn N), IsProbabilityMeasure θ → (∀ᵐ g ∂θ, ContinuousLinearMap.adjoint g * g = 1) → (∀ k : Rn N →L[ℝ] Rn N, ContinuousLinearMap.adjoint k * k = 1 → Measure.map (fun g ↦ g * k) θ = θ) → ∀ V : Submodule ℝ (Rn N), finrank ℝ V = n + 1 → 0 < μHE[n] {x : Rn N | x ∈ V ∧ ‖x‖ = 1} → μHE[n] {x : Rn N | x ∈ V ∧ ‖x‖ = 1} < ∞ → ∀ ζ ∈ V, ‖ζ‖ = 1 → θ {g | (a, g * V.starProjection * ContinuousLinearMap.adjoint g, g ζ) ∈ Bad} = 0`

## Sibling prerequisites

- `root.besicovitch_federer-a1.cone_trichotomy-a1.frame_averaging-a1.haar_stabilizer-a1`
- `root.besicovitch_federer-a1.cone_trichotomy-a1.frame_averaging-a1.stabilizer_orbit_null-a1`
- `root.besicovitch_federer-a1.cone_trichotomy-a1.frame_averaging-a1.coset_fubini-a1`
- `root.besicovitch_federer-a1.cone_trichotomy-a1.frame_averaging-a1.orthogonal_conj_projection-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
