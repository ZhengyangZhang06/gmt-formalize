# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.besicovitch_federer-a1.cone_trichotomy-a1.frame_averaging-a1.orthogonal_conj_projection-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-besicovitch-federer-a1-cone-trichotomy-a1-frame-averaging-a1-ort-b8943cb2b6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.besicovitch_federer-a1.cone_trichotomy-a1.frame_averaging-a1`
- Child key: `orthogonal_conj_projection`
- Declaration: `Submission.bf_starProjection_map_orthogonal`
- Exact Lean type: `∀ (N : ℕ) (g : Rn N →L[ℝ] Rn N), ContinuousLinearMap.adjoint g * g = 1 → ∀ V : Submodule ℝ (Rn N), (V.map (g : Rn N →ₗ[ℝ] Rn N)).starProjection = g * V.starProjection * ContinuousLinearMap.adjoint g ∧ finrank ℝ (V.map (g : Rn N →ₗ[ℝ] Rn N)) = finrank ℝ V`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
