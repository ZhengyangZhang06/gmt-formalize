# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.besicovitch_federer-a1.cone_density_positive-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-besicovitch-federer-a1-cone-density-positive-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.besicovitch_federer-a1`
- Child key: `cone_density_positive`
- Declaration: `Submission.bf_coneDensity_zero_null`
- Exact Lean type: `∀ (n ℓ : ℕ), 0 < n → ∀ (W : Submodule ℝ (Rn (n + ℓ))), finrank ℝ W = n → ∀ A : Set (Rn (n + ℓ)), PurelyUnrectifiable n A → ∀ δ : ℝ, 0 < δ → μHE[n] {a | a ∈ A ∧ ∀ c : ℝ, 0 < c → ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s < ε → ∀ r : ℝ, 0 < r → r < δ → μHE[n] (A ∩ ({x | ‖W.starProjection (x - a)‖ < s * ‖x - a‖} ∩ Metric.ball a r)) ≤ ENNReal.ofReal (c * (r * s) ^ n)} = 0`

## Sibling prerequisites

- `root.besicovitch_federer-a1.cone_mass_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
