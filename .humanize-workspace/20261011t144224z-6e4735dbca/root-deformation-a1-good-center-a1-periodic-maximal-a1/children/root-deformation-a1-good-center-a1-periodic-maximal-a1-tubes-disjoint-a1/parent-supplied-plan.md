# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.good_center-a1.periodic_maximal-a1.tubes_disjoint-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-good-center-a1-periodic-maximal-a1-tubes-disjoint-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.good_center-a1.periodic_maximal-a1`
- Child key: `tubes_disjoint`
- Declaration: `Submission.dgc_pm_lattice_tubes_disjoint`
- Exact Lean type: `∀ (ι : Type) [Fintype ι] (g₀ b b' : EuclideanSpace ℝ ι) (σ σ' : ℝ), dist b g₀ < 1 / 4 → dist b' g₀ < 1 / 4 → 0 < σ → σ < 1 / 4 → 0 < σ' → σ' < 1 / 4 → Disjoint (closedBall b σ) (closedBall b' σ') → Disjoint {y : EuclideanSpace ℝ ι | ∃ z : ι → ℤ, ∑ i, (y i - b i - z i) ^ 2 < σ ^ 2} {y : EuclideanSpace ℝ ι | ∃ z : ι → ℤ, ∑ i, (y i - b' i - z i) ^ 2 < σ' ^ 2}`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
