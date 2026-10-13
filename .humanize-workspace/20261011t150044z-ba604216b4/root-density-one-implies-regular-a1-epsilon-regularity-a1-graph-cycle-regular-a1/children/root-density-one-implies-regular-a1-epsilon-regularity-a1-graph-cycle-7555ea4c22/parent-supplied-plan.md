# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.graph_measure_bounds-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-7555ea4c22/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1`
- Child key: `graph_measure_bounds`
- Declaration: `Submission.dgcr_graph_measure_bounds`
- Exact Lean type: `∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (u : Euclid n → Euclid k) (z : Euclid (n + k)) (s : ℝ), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → 0 < s → ContDiffOn ℝ 1 u (ball 0 s) → (∀ (A : Set (Euclid n)) (g : Euclid (n + k) → ℝ≥0∞), MeasurableSet A → A ⊆ ball 0 s → Measurable g → ∫⁻ v in A, g (z + ι v + ι' (u v)) ≤ ∫⁻ x in (fun v => z + ι v + ι' (u v)) '' A, g x ∂μHE[n]) ∧ ∀ t : ℝ, t < s → μHE[n] ((fun v => z + ι v + ι' (u v)) '' closedBall (0 : Euclid n) t) ≠ ∞`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
