# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.first_rectifiability-a1.tangent_graph_cover_all-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-tangent-graph-cover-all-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.first_rectifiability-a1`
- Child key: `tangent_graph_cover_all`
- Declaration: `Submission.frt_tangent_points_flat_graph_cover`
- Exact Lean type: `∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U), (∀ L : ℝ, 0 < L → L ≤ 1 → ∀ P : Grassmannian N n, ∃ Γ : ℕ → Set (Euclidean N), (∀ i, IsClosed (Γ i)) ∧ (∀ i, ∀ y ∈ Γ i, ∀ z ∈ Γ i, ‖(y - z) - Grassmannian.project P (y - z)‖ ≤ L * ‖Grassmannian.project P (y - z)‖) ∧ ∀ (x : Euclidean N) (T : Grassmannian N n) (θ : ℝ), HasTangentPlane V x T θ → (∀ v : Euclidean N, ‖Grassmannian.project T v - Grassmannian.project P v‖ ≤ L / 4 * ‖v‖) → ∃ i, x ∈ Γ i) → ∀ L : ℝ, 0 < L → L ≤ 1 → ∃ C : Set (Grassmannian N n × Set (Euclidean N)), C.Countable ∧ (∀ c ∈ C, IsClosed c.2 ∧ ∀ y ∈ c.2, ∀ z ∈ c.2, ‖(y - z) - Grassmannian.project c.1 (y - z)‖ ≤ L * ‖Grassmannian.project c.1 (y - z)‖) ∧ {x | ∃ (T : Grassmannian N n) (θ : ℝ), HasTangentPlane V x T θ} ⊆ ⋃ c ∈ C, c.2`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
