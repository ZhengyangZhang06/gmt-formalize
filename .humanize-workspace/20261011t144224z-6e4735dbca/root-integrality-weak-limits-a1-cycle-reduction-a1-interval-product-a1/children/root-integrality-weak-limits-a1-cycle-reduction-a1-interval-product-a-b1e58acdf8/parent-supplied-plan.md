# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_tangent-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-b1e58acdf8/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1`
- Child key: `product_tangent`
- Declaration: `Submission.iwl_cr_ip_product_weighted_tangent`
- Exact Lean type: `∀ (P m : ℕ), (∀ A : Set (Eucl P), NullMeasurableSet A (μHE[m] : Measure (Eucl P)) → CountablyRectifiable m A → (∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (A ∩ K) < ∞) → (μHE[m + 1] : Measure (Eucl (P + 1))).restrict {y | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ A} = Measure.map (fun p : ℝ × Eucl P => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons p.1 (EuclideanSpace.equiv (Fin P) ℝ p.2))) ((volume : Measure ℝ).prod ((μHE[m] : Measure (Eucl P)).restrict A))) → ∀ (M : Set (Eucl P)) (θ : Eucl P → ℝ) (x : Eucl P) (τ : Fin m → Eucl P) (s₀ : ℝ), NullMeasurableSet M (μHE[m] : Measure (Eucl P)) → CountablyRectifiable m M → (∀ K : Set (Eucl P), IsCompact K → (μHE[m] : Measure (Eucl P)) (M ∩ K) < ∞) → (∀ z ∈ M, 0 ≤ θ z) → (∀ K : Set (Eucl P), IsCompact K → IntegrableOn θ (M ∩ K) (μHE[m] : Measure (Eucl P))) → Orthonormal ℝ τ → HasWeightedApproximateTangentSpaceAt m M θ x (Submodule.span ℝ (range τ)) → s₀ ∈ Ioo (0 : ℝ) 1 → HasWeightedApproximateTangentSpaceAt (m + 1) {y : Eucl (P + 1) | (EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)) ∈ M ∧ EuclideanSpace.equiv (Fin (P + 1)) ℝ y 0 ∈ Ioo (0 : ℝ) 1} (fun y : Eucl (P + 1) => θ ((EuclideanSpace.equiv (Fin P) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (P + 1)) ℝ y)))) ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons s₀ (EuclideanSpace.equiv (Fin P) ℝ x))) (Submodule.span ℝ (range (Fin.cons (EuclideanSpace.single 0 1 : Eucl (P + 1)) (fun i => (EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin P) ℝ (τ i)))) : Fin (m + 1) → Eucl (P + 1))))`

## Sibling prerequisites

- `root.flat_iff_weak-a1.tangent_locality-a1.blowup_change_of_variables-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
