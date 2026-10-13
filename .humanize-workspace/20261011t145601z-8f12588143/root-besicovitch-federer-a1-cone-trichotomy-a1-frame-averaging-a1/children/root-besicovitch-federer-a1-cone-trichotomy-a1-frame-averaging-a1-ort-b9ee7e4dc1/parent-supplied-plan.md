# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.besicovitch_federer-a1.cone_trichotomy-a1.frame_averaging-a1.orthogonal_plane_transitive-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-besicovitch-federer-a1-cone-trichotomy-a1-frame-averaging-a1-ort-b9ee7e4dc1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.besicovitch_federer-a1.cone_trichotomy-a1.frame_averaging-a1`
- Child key: `orthogonal_plane_transitive`
- Declaration: `Submission.bf_orthogonal_exists_map_eq`
- Exact Lean type: `∀ (N : ℕ) (W₀ W : Submodule ℝ (Rn N)), finrank ℝ W₀ = finrank ℝ W → ∃ h : Rn N →L[ℝ] Rn N, ContinuousLinearMap.adjoint h * h = 1 ∧ W₀.map (h : Rn N →ₗ[ℝ] Rn N) = W`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
