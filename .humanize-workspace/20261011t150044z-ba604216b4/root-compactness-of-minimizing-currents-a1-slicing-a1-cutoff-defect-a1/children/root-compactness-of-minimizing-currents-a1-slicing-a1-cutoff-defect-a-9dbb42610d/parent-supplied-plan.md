# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.slicing-a1.cutoff_defect-a1.leibniz-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-slicing-a1-cutoff-defect-a-9dbb42610d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.slicing-a1.cutoff_defect-a1`
- Child key: `leibniz`
- Declaration: `Submission.cmcs_cd_extDeriv_smul_leibniz`
- Exact Lean type: `∀ (P k : ℕ) (g : Euclid P → ℝ) (η : DifferentialForm (Euclid P) k) (x : Euclid P), DifferentiableAt ℝ g x → DifferentiableAt ℝ η x → exteriorDerivative (fun y => g y • η y) x = g x • exteriorDerivative η x + ContinuousAlternatingMap.alternatizeUncurryFin ((fderiv ℝ g x).smulRight (η x))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
