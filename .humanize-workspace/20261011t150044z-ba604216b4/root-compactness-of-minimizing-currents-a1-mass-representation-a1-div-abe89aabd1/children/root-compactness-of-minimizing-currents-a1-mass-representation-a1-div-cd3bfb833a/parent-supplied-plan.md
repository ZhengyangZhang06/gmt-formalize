# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.mass_representation-a1.divergence_form-a1.contraction_extderiv-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-mass-representation-a1-div-cd3bfb833a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.mass_representation-a1.divergence_form-a1`
- Child key: `contraction_extderiv`
- Declaration: `Submission.cmr_df_extDeriv_smul_curryLeft`
- Exact Lean type: `∀ (P m : ℕ) (θ : Covector (Euclid P) (m + 1)) (b : Euclid P → ℝ) (G : Euclid P → Euclid P) (x : Euclid P), DifferentiableAt ℝ b x → DifferentiableAt ℝ G x → ∀ w : Fin (m + 1) → Euclid P, exteriorDerivative (fun y => b y • ContinuousAlternatingMap.curryLeft θ (G y)) x w = ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) * (fderiv ℝ b x (w i) * θ (Fin.cons (G x) (i.removeNth w)) + b x * θ (Fin.cons (fderiv ℝ G x (w i)) (i.removeNth w)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
