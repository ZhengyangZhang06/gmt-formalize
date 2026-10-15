# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.flat_convergence-a1.localize-a1.mass_le_measure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-locali-be968f7b5a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.localize-a1`
- Child key: `mass_le_measure`
- Declaration: `Submission.cmc_fcl_massOn_le_measure_inter`
- Exact Lean type: `∀ (P d : ℕ) (U : Set (Euclid P)) (X : GeometricCurrentOn U d) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P d) (E V : Set (Euclid P)), (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) d, |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U d, X ω = ∫ x in E, ξ x ((ω : DifferentialForm (Euclid P) d) x) ∂μ) → X.massOn V ≤ μ (E ∩ V)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
