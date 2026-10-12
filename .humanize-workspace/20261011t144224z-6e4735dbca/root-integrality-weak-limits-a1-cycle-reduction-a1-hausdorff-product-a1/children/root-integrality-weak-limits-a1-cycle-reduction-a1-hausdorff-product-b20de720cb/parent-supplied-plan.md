# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.cycle_reduction-a1.hausdorff_product-a1.piece_product-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-hausdorff-product-b20de720cb/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.cycle_reduction-a1.hausdorff_product-a1`
- Child key: `piece_product`
- Declaration: `Submission.iwl_cr_hp_piece_product`
- Exact Lean type: `∀ (P m : ℕ) (G : Eucl m → Eucl P) (K : ℝ≥0) (B : Set (Eucl m)), LipschitzWith K G → MeasurableSet B → InjOn G B → (∀ b ∈ B, DifferentiableAt ℝ G b) → ∀ g : Eucl (P + 1) → ℝ≥0∞, Measurable g → Measurable (fun s : ℝ => ∫⁻ x in G '' B, g ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) ∂(μHE[m] : Measure (Eucl P))) ∧ ∫⁻ y in {y | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ G '' B}, g y ∂(μHE[m + 1] : Measure (Eucl (P + 1))) = ∫⁻ s : ℝ, ∫⁻ x in G '' B, g ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) ∂(μHE[m] : Measure (Eucl P))`

## Sibling prerequisites

- `root.integrality_weak_limits-a1.cycle_reduction-a1.hausdorff_product-a1.lift_gram_det-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
