# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.besicovitch_federer-a1.cone_mass_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-besicovitch-federer-a1-cone-mass-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.besicovitch_federer-a1`
- Child key: `cone_mass_bound`
- Declaration: `Submission.bf_coneMass_ball_le`
- Exact Lean type: `∀ (n ℓ : ℕ), 0 < n → ∀ (W : Submodule ℝ (Rn (n + ℓ))), finrank ℝ W = n → ∀ (s δ c : ℝ), 0 < s → s < 1 → 0 < δ → 0 ≤ c → ∀ B : Set (Rn (n + ℓ)), PurelyUnrectifiable n B → (∀ x ∈ B, ∀ r : ℝ, 0 < r → r < δ → μHE[n] (B ∩ ({y | ‖W.starProjection (y - x)‖ < s * ‖y - x‖} ∩ Metric.ball x r)) ≤ ENNReal.ofReal (c * (r * s) ^ n)) → ∀ a : Rn (n + ℓ), μHE[n] (B ∩ Metric.ball a (δ / 8)) ≤ ENNReal.ofReal (2 * 15 ^ n * c * δ ^ n)`

## Sibling prerequisites

- `root.besicovitch_federer-a1.cone_free_rectifiable-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
