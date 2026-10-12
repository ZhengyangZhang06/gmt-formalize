# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.varifold_tangents-a1.limit_ball_mass-a1.vague_cylinder_bounds-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-varifold-tangents-a1-limit-ball-mass-a1-vague-cylinder-bounds-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.varifold_tangents-a1.limit_ball_mass-a1`
- Child key: `vague_cylinder_bounds`
- Declaration: `Submission.varifold_tangents_lbm_vague_cylinder_bounds`
- Exact Lean type: `∀ (N n : ℕ) (μs : ℕ → Measure (Euclidean N × Grassmannian N n)) (μ : Measure (Euclidean N × Grassmannian N n)) (a b : ℝ) (La Lb : ℝ≥0∞), VagueConverges μs μ → a < b → μ (closedBall (0 : Euclidean N) b ×ˢ (univ : Set (Grassmannian N n))) ≠ ∞ → Tendsto (fun j ↦ μs j (closedBall (0 : Euclidean N) a ×ˢ (univ : Set (Grassmannian N n)))) atTop (𝓝 La) → Tendsto (fun j ↦ μs j (closedBall (0 : Euclidean N) b ×ˢ (univ : Set (Grassmannian N n)))) atTop (𝓝 Lb) → Lb ≠ ∞ → μ (closedBall (0 : Euclidean N) a ×ˢ (univ : Set (Grassmannian N n))) ≤ Lb ∧ La ≤ μ (closedBall (0 : Euclidean N) b ×ˢ (univ : Set (Grassmannian N n)))`

## Sibling prerequisites

- `root.varifold_tangents-a1.limit_ball_mass-a1.cylinder_cutoff-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
