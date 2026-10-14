# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.piece_current-a1.regular_reduction-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-835779a080/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.piece_current-a1`
- Child key: `regular_reduction`
- Declaration: `Submission.cmcdt_lpi_pc_regular_part_reduction`
- Exact Lean type: `∀ (P n : ℕ) (L : NNReal) (H : Euclid n → Euclid P) (A : Set (Euclid n)) (g : Euclid n → ℤ), LipschitzWith L H → MeasurableSet A → Measurable g → IntegrableOn (fun u => (g u : ℝ)) A → MeasurableSet {u | u ∈ A ∧ DifferentiableAt ℝ H u ∧ Injective (fderiv ℝ H u) ∧ g u ≠ 0} ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) n, IntegrableOn (fun u => (g u : ℝ) * (ω : DifferentialForm (Euclid P) n) (H u) (fun a => fderiv ℝ H u (EuclideanSpace.single a 1))) A ∧ ∫ u in A, (g u : ℝ) * (ω : DifferentialForm (Euclid P) n) (H u) (fun a => fderiv ℝ H u (EuclideanSpace.single a 1)) = ∫ u in {u | u ∈ A ∧ DifferentiableAt ℝ H u ∧ Injective (fderiv ℝ H u) ∧ g u ≠ 0}, (g u : ℝ) * (ω : DifferentialForm (Euclid P) n) (H u) (fun a => fderiv ℝ H u (EuclideanSpace.single a 1))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
