# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.besicovitch_federer-a1.cone_mass_bound-a1.ball_packing-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-besicovitch-federer-a1-cone-mass-bound-a1-ball-packing-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.besicovitch_federer-a1.cone_mass_bound-a1`
- Child key: `ball_packing`
- Declaration: `Submission.bf_coneMass_subspace_ball_packing`
- Exact Lean type: `∀ (n N : ℕ) (W : Submodule ℝ (Rn N)), finrank ℝ W = n → ∀ (ι : Type) (T : Set ι) (w : ι → Rn N) (ρ : ι → ℝ) (w₀ : Rn N) (R : ℝ), T.Countable → (∀ i ∈ T, w i ∈ W) → w₀ ∈ W → (∀ i ∈ T, 0 < ρ i) → T.PairwiseDisjoint (fun i ↦ Metric.ball (w i) (ρ i)) → (∀ i ∈ T, Metric.ball (w i) (ρ i) ⊆ Metric.ball w₀ R) → ∑' i : T, ENNReal.ofReal (ρ i ^ n) ≤ ENNReal.ofReal (R ^ n)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
