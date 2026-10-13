# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.lipschitz_approximation-a1.hole_measure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-37fdf6ae94/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.lipschitz_approximation-a1`
- Child key: `hole_measure`
- Declaration: `Submission.dorag_lip_graph_hole_measure_bound`
- Exact Lean type: `∀ (n k : ℕ) (μ : Measure (Euclid (n + k))) (e : Euclid (n + k) → ℝ) (F A B : Set (Euclid (n + k))) (K : ℝ≥0∞) (C₉ R₀ : ℝ), MeasurableSet B → A ⊆ F → (∀ η ∈ A, ∀ r : ℝ, 0 < r → μHE[n] (F ∩ closedBall η r) ≤ K * ENNReal.ofReal (r ^ n)) → (∀ η ∈ A, ∃ s : ℝ, 0 < s ∧ s ≤ R₀ ∧ closedBall η (3 * s) ⊆ B ∧ ENNReal.ofReal (s ^ n) ≤ ENNReal.ofReal C₉ * (μ (closedBall η (3 * s) \ F) + ∫⁻ x in closedBall η (3 * s), ENNReal.ofReal (e x) ∂μ)) → μHE[n] A ≤ K * ENNReal.ofReal (15 ^ n * C₉) * (μ (B \ F) + ∫⁻ x in B, ENNReal.ofReal (e x) ∂μ)`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.lipschitz_approximation-a1.vitali_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
