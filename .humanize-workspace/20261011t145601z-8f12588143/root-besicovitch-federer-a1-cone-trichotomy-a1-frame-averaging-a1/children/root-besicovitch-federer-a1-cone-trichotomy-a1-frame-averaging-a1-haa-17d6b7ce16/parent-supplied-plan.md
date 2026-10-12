# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.besicovitch_federer-a1.cone_trichotomy-a1.frame_averaging-a1.haar_stabilizer-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-besicovitch-federer-a1-cone-trichotomy-a1-frame-averaging-a1-haa-17d6b7ce16/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.besicovitch_federer-a1.cone_trichotomy-a1.frame_averaging-a1`
- Child key: `haar_stabilizer`
- Declaration: `Submission.bf_orthStabilizer_haar_exists`
- Exact Lean type: `∀ (N : ℕ) (U : Submodule ℝ (Rn N)), ∃ θ : Measure (Rn N →L[ℝ] Rn N), IsProbabilityMeasure θ ∧ (∀ᵐ g ∂θ, ContinuousLinearMap.adjoint g * g = 1 ∧ ∀ x ∈ U, g x = x) ∧ ∀ k : Rn N →L[ℝ] Rn N, ContinuousLinearMap.adjoint k * k = 1 → (∀ x ∈ U, k x = x) → Measure.map (fun g ↦ k * g) θ = θ ∧ Measure.map (fun g ↦ g * k) θ = θ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
