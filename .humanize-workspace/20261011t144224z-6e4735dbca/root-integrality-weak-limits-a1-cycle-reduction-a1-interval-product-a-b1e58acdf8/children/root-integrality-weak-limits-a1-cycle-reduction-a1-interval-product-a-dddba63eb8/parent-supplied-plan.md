# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_tangent-a1.product_measure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-dddba63eb8/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_tangent-a1`
- Child key: `product_measure`
- Declaration: `Submission.iwl_cr_ip_wt_product_measure`
- Exact Lean type: `∀ (P m : ℕ), (∀ A : Set (Eucl P), NullMeasurableSet A (μHE[m] : Measure (Eucl P)) → CountablyRectifiable m A → (∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (A ∩ K) < ∞) → (μHE[m + 1] : Measure (Eucl (P + 1))).restrict {y | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ A} = Measure.map (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) ((volume : Measure ℝ).prod ((μHE[m] : Measure (Eucl P)).restrict A))) → ∀ M : Set (Eucl P), NullMeasurableSet M (μHE[m] : Measure (Eucl P)) → CountablyRectifiable m M → (∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (M ∩ K) < ∞) → (μHE[m + 1] : Measure (Eucl (P + 1))).restrict {y : Eucl (P + 1) | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ M ∧ EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1} = Measure.map (fun p : ℝ × Eucl P => ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2)))) (((volume : Measure ℝ).restrict (Ioo (0 : ℝ) 1)).prod ((μHE[m] : Measure (Eucl P)).restrict M))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
