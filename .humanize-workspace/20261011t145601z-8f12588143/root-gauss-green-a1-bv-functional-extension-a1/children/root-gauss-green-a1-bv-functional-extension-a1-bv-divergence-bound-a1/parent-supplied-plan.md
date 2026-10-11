# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.gauss_green-a1.bv_functional_extension-a1.bv_divergence_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-gauss-green-a1-bv-functional-extension-a1-bv-divergence-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.gauss_green-a1.bv_functional_extension-a1`
- Child key: `bv_divergence_bound`
- Declaration: `Submission.gaussGreenRep_divergence_integral_local_bound`
- Exact Lean type: `∀ (N : ℕ) (U E : Set (Rn N)), IsOpen U → NullMeasurableSet E volume → HasLocallyFinitePerimeter U E → ∀ K : Set (Rn N), IsCompact K → K ⊆ U → ∃ C : ℝ, 0 ≤ C ∧ ∀ g : Rn N → Rn N, ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ K → ∀ M : ℝ, (∀ x, ‖g x‖ ≤ M) → |∫ x in E ∩ U, Poincare.SimonGMT.Chapter02.euclideanDivergence g x| ≤ C * M`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
