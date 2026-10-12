# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tangent_graph_cover-a1.cone_graph_cover-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-tangent-graph-cover-a1-cone-graph-cover-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tangent_graph_cover-a1`
- Child key: `cone_graph_cover`
- Declaration: `Submission.tgc_cone_density_graph_cover`
- Exact Lean type: `∀ (N n : ℕ) (L : ℝ) (μ : Measure (Euclidean N)) (P : Grassmannian N n) (A : Set (Euclidean N)), 0 < L → L ≤ 1 → (∀ x ∈ A, ∃ T : Grassmannian N n, (∀ v : Euclidean N, ‖Grassmannian.project T v - Grassmannian.project P v‖ ≤ L / 4 * ‖v‖) ∧ (∃ c : ℝ≥0∞, 0 < c ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), c * ENNReal.ofReal t ^ n ≤ μ (closedBall x t)) ∧ ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ t in 𝓝[>] (0 : ℝ), μ {y | y ∈ closedBall x t ∧ L / 16 * ‖y - x‖ ≤ ‖(y - x) - Grassmannian.project T (y - x)‖} ≤ ε * ENNReal.ofReal t ^ n) → ∃ Γ : ℕ → Set (Euclidean N), (∀ i, IsClosed (Γ i)) ∧ (∀ i, ∀ y ∈ Γ i, ∀ z ∈ Γ i, ‖(y - z) - Grassmannian.project P (y - z)‖ ≤ L * ‖Grassmannian.project P (y - z)‖) ∧ ∀ x ∈ A, ∃ i, x ∈ Γ i`

## Sibling prerequisites

- `root.tangent_graph_cover-a1.cone_linear_algebra-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
