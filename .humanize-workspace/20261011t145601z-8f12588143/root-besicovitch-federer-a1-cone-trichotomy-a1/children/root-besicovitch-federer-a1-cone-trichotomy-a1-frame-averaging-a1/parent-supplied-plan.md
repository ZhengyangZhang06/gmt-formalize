# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.besicovitch_federer-a1.cone_trichotomy-a1.frame_averaging-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-besicovitch-federer-a1-cone-trichotomy-a1-frame-averaging-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.besicovitch_federer-a1.cone_trichotomy-a1`
- Child key: `frame_averaging`
- Declaration: `Submission.bf_frameAveraging_null`
- Exact Lean type: `∀ (n ℓ : ℕ), 0 < n → 0 < ℓ → ∀ μ : Measure (Rn (n + ℓ)), IsFiniteMeasure μ → ∀ (Exc : Set (Rn (n + ℓ) × (Rn (n + ℓ) →L[ℝ] Rn (n + ℓ)))) (Bad : Set (Rn (n + ℓ) × (Rn (n + ℓ) →L[ℝ] Rn (n + ℓ)) × Rn (n + ℓ))), MeasurableSet Exc → MeasurableSet Bad → (∀ (a : Rn (n + ℓ)) (H : Submodule ℝ (Rn (n + ℓ))), finrank ℝ H = n + 1 → μHE[n] {θ | θ ∈ H ∧ ‖θ‖ = 1 ∧ (a, H.starProjection, θ) ∈ Bad} = 0) → (∀ (a : Rn (n + ℓ)) (W : Submodule ℝ (Rn (n + ℓ))), finrank ℝ W = n → (a, W.starProjection) ∈ Exc → ∀ u : Fin ℓ → Rn (n + ℓ), Orthonormal ℝ u → (∀ j, u j ∈ Wᗮ) → ∃ j, (a, (W ⊔ Submodule.span ℝ {u j}).starProjection, u j) ∈ Bad) → ForAlmostAllProjections (n + ℓ) n (fun p ↦ μ {a | (a, p) ∈ Exc} = 0)`

## Sibling prerequisites

- `root.besicovitch_federer-a1.cone_trichotomy-a1.sphere_cap_bounds-a1`
- `root.besicovitch_federer-a1.cone_trichotomy-a1.frame_projection_continuous-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
