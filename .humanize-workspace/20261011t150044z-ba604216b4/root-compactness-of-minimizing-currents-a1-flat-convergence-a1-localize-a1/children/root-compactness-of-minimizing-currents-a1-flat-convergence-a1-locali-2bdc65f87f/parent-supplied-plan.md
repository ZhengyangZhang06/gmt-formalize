# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.flat_convergence-a1.localize-a1.imrep_data-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-locali-2bdc65f87f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.localize-a1`
- Child key: `imrep_data`
- Declaration: `Submission.cmc_fcl_imrep_integral_data`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (Z : GeometricCurrentOn U n) (R : IMRep U n), R.Represents Z → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → R.measure K < ∞) ∧ AEStronglyMeasurable R.orient R.measure ∧ ((∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α) → ∀ᵐ x ∂R.measure, ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α) ∧ ∀ ω : TestFormOn U n, Z ω = ∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂R.measure`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
