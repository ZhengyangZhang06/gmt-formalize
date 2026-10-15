# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.piece_current-a1.piece_multiplicity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-8678675ff1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.piece_current-a1`
- Child key: `piece_multiplicity`
- Declaration: `Submission.cmcdt_lpi_pc_piece_multiplicity`
- Exact Lean type: `∀ (P n : ℕ) (L : NNReal) (H : Euclid n → Euclid P) (B : Set (Euclid n)) (g : Euclid n → ℤ), LipschitzWith L H → MeasurableSet B → InjOn H B → (∀ a ∈ B, DifferentiableAt ℝ H a ∧ Injective (fderiv ℝ H a)) → Measurable g → IntegrableOn (fun u => (g u : ℝ)) B → (∀ u ∈ B, g u ≠ 0) → ∃ m : Euclid P → ℝ, Measurable m ∧ (∀ y, ∃ z : ℤ, m y = z) ∧ (∀ u ∈ B, m (H u) = g u) ∧ μHE[n] (H '' B) ≠ ∞ ∧ ∫⁻ y in H '' B, ‖m y‖ₑ ∂μHE[n] ≤ (L : ℝ≥0∞) ^ n * ∫⁻ u in B, ‖(g u : ℝ)‖ₑ`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.integrality-a1.piece_current-a1.measurable_inverse-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
