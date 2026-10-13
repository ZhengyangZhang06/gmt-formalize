# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.besicovitch_federer-a1.cone_density_infinite-a1.plane_vitali_cover-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-besicovitch-federer-a1-cone-density-infinite-a1-plane-vitali-cover-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.besicovitch_federer-a1.cone_density_infinite-a1`
- Child key: `plane_vitali_cover`
- Declaration: `Submission.bf_plane_vitali_disjoint_cover`
- Exact Lean type: `∀ (n N : ℕ) (W : Submodule ℝ (Rn N)), finrank ℝ W = n → ∀ (ι : Type) (S : Set (Rn N)) (t : Set ι) (c : ι → Rn N) (ρ : ι → ℝ), S ⊆ (W : Set (Rn N)) → (∀ i ∈ t, c i ∈ W ∧ 0 < ρ i) → (∀ x ∈ S, ∀ ε : ℝ, 0 < ε → ∃ i ∈ t, c i = x ∧ ρ i ≤ ε) → ∃ u ⊆ t, u.Countable ∧ u.PairwiseDisjoint (fun i ↦ (W : Set (Rn N)) ∩ Metric.closedBall (c i) (ρ i)) ∧ μHE[n] (S \ ⋃ i ∈ u, ((W : Set (Rn N)) ∩ Metric.closedBall (c i) (ρ i))) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
