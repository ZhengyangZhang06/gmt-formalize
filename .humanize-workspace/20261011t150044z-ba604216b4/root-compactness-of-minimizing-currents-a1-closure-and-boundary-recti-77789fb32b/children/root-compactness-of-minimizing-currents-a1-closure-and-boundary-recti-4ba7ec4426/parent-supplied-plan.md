# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.covering-a1.ball_cover-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-4ba7ec4426/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.covering-a1`
- Child key: `ball_cover`
- Declaration: `Submission.cbrldvc_exists_disjoint_closedBall_cover`
- Exact Lean type: `∀ (P : ℕ) (μ : Measure (Euclid P)) (Q : Euclid P → ℝ → Prop) (E W : Set (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → IsOpen W → E ⊆ W → (∀ x ∈ E, ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧ Q x ρ) → ∃ (t : Set (Euclid P)) (r : Euclid P → ℝ), t.Countable ∧ t ⊆ E ∧ (∀ x ∈ t, 0 < r x ∧ closedBall x (r x) ⊆ W ∧ Q x (r x)) ∧ t.PairwiseDisjoint (fun x => closedBall x (r x)) ∧ μ (E \ ⋃ x ∈ t, closedBall x (r x)) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
