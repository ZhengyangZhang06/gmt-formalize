# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rectifiability-a1.projection_null-a1.potential_form_derivative-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-projection-null-a1-potential-form-derivative-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rectifiability-a1.projection_null-a1`
- Child key: `potential_form_derivative`
- Declaration: `Submission.rpn_extDeriv_potential_form`
- Exact Lean type: `∀ (P m : ℕ) (L : Eucl P →L[ℝ] Eucl (m + 1)) (f : Eucl P → ℝ) (ψ : Fin (m + 1) → Eucl (m + 1) → ℝ) (x : Eucl P), DifferentiableAt ℝ f x → (∀ j, DifferentiableAt ℝ (ψ j) (L x)) → extDeriv (fun z => ∑ j : Fin (m + 1), ((-1 : ℝ) ^ (j : ℕ) * (f z * ψ j (L z))) • wedgeCovectors m (fun i => (EuclideanSpace.proj (j.succAbove i) : Eucl (m + 1) →L[ℝ] ℝ).comp L)) x = (f x * ∑ j : Fin (m + 1), fderiv ℝ (ψ j) (L x) (EuclideanSpace.single j (1 : ℝ))) • wedgeCovectors (m + 1) (fun i => (EuclideanSpace.proj i : Eucl (m + 1) →L[ℝ] ℝ).comp L) + ∑ j : Fin (m + 1), ((-1 : ℝ) ^ (j : ℕ) * ψ j (L x)) • wedgeCovectors (m + 1) (Fin.cons (fderiv ℝ f x) (fun i => (EuclideanSpace.proj (j.succAbove i) : Eucl (m + 1) →L[ℝ] ℝ).comp L) : Fin (m + 1) → (Eucl P →L[ℝ] ℝ))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
