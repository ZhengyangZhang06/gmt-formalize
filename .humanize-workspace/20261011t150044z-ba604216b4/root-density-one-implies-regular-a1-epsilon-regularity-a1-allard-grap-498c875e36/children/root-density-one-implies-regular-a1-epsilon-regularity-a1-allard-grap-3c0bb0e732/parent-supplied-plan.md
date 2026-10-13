# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.density_bounds-a1.lower_density_mult-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-3c0bb0e732/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.density_bounds-a1`
- Child key: `lower_density_mult`
- Declaration: `Submission.dorag_dbs_lower_density_ge_mult`
- Exact Lean type: `∀ (P n : ℕ) (U W : Set (Euclid P)) (R : IMRep U n), 0 < n → IsOpen W → W ⊆ U → ∀ᵐ x ∂(μHE[n].restrict R.carrier), x ∈ W → ∀ c : ℝ, c < R.mult x → ∀ᶠ t in 𝓝[>] (0 : ℝ), ENNReal.ofReal c * unitBallVolume n * ENNReal.ofReal (t ^ n) ≤ R.measure (closedBall x t)`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.density_bounds-a1.tangent_lower_density-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.density_bounds-a1.localized_density-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
