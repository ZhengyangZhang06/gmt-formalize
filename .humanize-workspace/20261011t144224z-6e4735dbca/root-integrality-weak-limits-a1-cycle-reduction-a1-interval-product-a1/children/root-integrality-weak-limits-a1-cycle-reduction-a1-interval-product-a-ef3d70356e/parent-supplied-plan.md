# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.measure_identity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-ef3d70356e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1`
- Child key: `measure_identity`
- Declaration: `Submission.iwl_cr_ip_restrict_preimage_eq_map`
- Exact Lean type: `∀ (P m : ℕ) (A : Set (Eucl P)), (∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (A ∩ K) < ∞) → (∀ g : Eucl (P + 1) → ℝ≥0∞, Measurable g → ∫⁻ y in {y | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ A}, g y ∂(μHE[m + 1] : Measure (Eucl (P + 1))) = ∫⁻ s : ℝ, ∫⁻ x in A, g ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin P) ℝ x))) ∂(μHE[m] : Measure (Eucl P))) → (μHE[m + 1] : Measure (Eucl (P + 1))).restrict {y | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ A} = Measure.map (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) ((volume : Measure ℝ).prod ((μHE[m] : Measure (Eucl P)).restrict A))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
