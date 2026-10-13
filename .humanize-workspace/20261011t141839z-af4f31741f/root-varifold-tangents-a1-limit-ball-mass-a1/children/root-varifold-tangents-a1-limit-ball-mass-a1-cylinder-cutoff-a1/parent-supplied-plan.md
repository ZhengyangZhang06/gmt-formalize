# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.varifold_tangents-a1.limit_ball_mass-a1.cylinder_cutoff-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-varifold-tangents-a1-limit-ball-mass-a1-cylinder-cutoff-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.varifold_tangents-a1.limit_ball_mass-a1`
- Child key: `cylinder_cutoff`
- Declaration: `Submission.varifold_tangents_lbm_exists_cylinder_cutoff`
- Exact Lean type: `∀ (N n : ℕ) (a b : ℝ), a < b → ∃ F : C_c(Euclidean N × Grassmannian N n, ℝ), ∀ ν : Measure (Euclidean N × Grassmannian N n), ν (closedBall (0 : Euclidean N) b ×ˢ (univ : Set (Grassmannian N n))) ≠ ∞ → ν (closedBall (0 : Euclidean N) a ×ˢ (univ : Set (Grassmannian N n))) ≤ ENNReal.ofReal (∫ z, F z ∂ν) ∧ ENNReal.ofReal (∫ z, F z ∂ν) ≤ ν (closedBall (0 : Euclidean N) b ×ˢ (univ : Set (Grassmannian N n)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
