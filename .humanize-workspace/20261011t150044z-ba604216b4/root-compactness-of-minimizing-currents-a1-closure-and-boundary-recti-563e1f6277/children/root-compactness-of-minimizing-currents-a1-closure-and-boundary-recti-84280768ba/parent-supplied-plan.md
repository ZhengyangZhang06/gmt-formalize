# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.rectifiable-a1.uniform_density-a1.cone_mass_closed-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-84280768ba/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.rectifiable-a1.uniform_density-a1`
- Child key: `cone_mass_closed`
- Declaration: `Submission.cbrr_ud_isClosed_cone_mass_le`
- Exact Lean type: `∀ (P : ℕ) (μ : Measure (Euclid P)) (F : Set (Euclid P)) (Q : Euclid P → Submodule ℝ (Euclid P)) (ρ : ℝ) (s : ℝ≥0∞), IsClosed F → ContinuousOn (fun x => (Q x).starProjection) F → IsClosed {x | x ∈ F ∧ μ ({z | 2 * ‖(Q x).starProjection (z - x)‖ < ‖z - x‖} ∩ ball x ρ) ≤ s}`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
