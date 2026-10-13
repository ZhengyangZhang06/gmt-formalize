# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.density_bounds-a1.localized_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-db831ac52f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.density_bounds-a1`
- Child key: `localized_density`
- Declaration: `Submission.dorag_dbs_localized_density_point`
- Exact Lean type: `∀ (P : ℕ) (W s : Set (Euclid P)) (ν : Measure (Euclid P)), IsOpen W → MeasurableSet s → (∀ K : Set (Euclid P), IsCompact K → K ⊆ W → ν K ≠ ∞) → ∀ᵐ x ∂ν.restrict s, x ∈ W → ∀ a : ℝ, a < 1 → ∀ᶠ t in 𝓝[>] (0 : ℝ), ENNReal.ofReal a * ν (closedBall x t) ≤ ν (s ∩ closedBall x t)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
