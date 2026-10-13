# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_mass_bound-a1.leibniz_bound-a1.extderiv_leibniz-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-leibniz-bound-a1-extderiv-leibniz-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_mass_bound-a1.leibniz_bound-a1`
- Child key: `extderiv_leibniz`
- Declaration: `Submission.slicing_mb_lb_extDeriv_smul`
- Exact Lean type: `∀ (P m : ℕ) (ψ : Eucl P → ℝ) (ω : DifferentialForm (Eucl P) m) (x : Eucl P), DifferentiableAt ℝ ψ x → DifferentiableAt ℝ ω x → exteriorDerivative (fun y => ψ y • ω y : DifferentialForm (Eucl P) m) x = ψ x • exteriorDerivative ω x + ContinuousAlternatingMap.alternatizeUncurryFin ((fderiv ℝ ψ x).smulRight (ω x))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
