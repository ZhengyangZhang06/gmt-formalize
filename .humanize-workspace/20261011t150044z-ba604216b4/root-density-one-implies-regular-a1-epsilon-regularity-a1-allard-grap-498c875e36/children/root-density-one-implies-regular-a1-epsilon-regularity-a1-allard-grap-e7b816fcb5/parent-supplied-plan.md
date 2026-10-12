# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.density_bounds-a1.mult_one-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-e7b816fcb5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.density_bounds-a1`
- Child key: `mult_one`
- Declaration: `Submission.dorag_dbs_mult_eq_one_of_density_lt_two`
- Exact Lean type: `∀ (P n : ℕ) (U W S : Set (Euclid P)) (R : IMRep U n) (c₀ : ℝ), 0 < n → IsOpen W → W ⊆ U → S ⊆ W → c₀ < 2 → (∀ x ∈ S, ∀ᶠ t in 𝓝[>] (0 : ℝ), R.measure (closedBall x t) ≤ ENNReal.ofReal c₀ * unitBallVolume n * ENNReal.ofReal (t ^ n)) → ∀ᵐ x ∂R.measure, x ∈ S → R.mult x = 1`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.density_bounds-a1.lower_density_mult-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
