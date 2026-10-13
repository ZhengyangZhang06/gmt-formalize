# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.graph_weak_equation-a1.graph_tangential_estimate-a1.lipschitz_ball_calculus-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-graph-weak-equation-a1-graph-tangential-est-bfb94e0301/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1.graph_weak_equation-a1.graph_tangential_estimate-a1`
- Child key: `lipschitz_ball_calculus`
- Declaration: `Submission.gte_lipschitz_ball_calculus`
- Exact Lean type: `∀ (n ℓ : ℕ) (f : Rn n → Rn ℓ) (K : ℝ≥0) (R : ℝ), LipschitzOnWith K f (closedBall 0 R) → MeasurableSet (ball (0 : Rn n) R ∩ {x | ¬DifferentiableAt ℝ f x}) ∧ volume (ball (0 : Rn n) R ∩ {x | ¬DifferentiableAt ℝ f x}) = 0 ∧ ∀ x ∈ ball (0 : Rn n) R, ‖fderiv ℝ f x‖ ≤ K ∧ (DifferentiableAt ℝ f x → ∀ (j : Fin ℓ) (v : Rn n), inner ℝ (gradient (fun y => f y j) x) v = fderiv ℝ f x v j)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
