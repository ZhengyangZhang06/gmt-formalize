# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_tangent-a1.slice_continuous-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-interval-product-a-94ec7e89b7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.cycle_reduction-a1.interval_product-a1.product_tangent-a1`
- Child key: `slice_continuous`
- Declaration: `Submission.iwl_cr_ip_wt_slice_continuous`
- Exact Lean type: `∀ (P m : ℕ) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (x : Eucl P), (∀ K : Set (Eucl P), IsCompact K → IntegrableOn θ (M ∩ K) (μHE[m] : Measure (Eucl P))) → ∀ f : Eucl (P + 1) → ℝ, Continuous f → HasCompactSupport f → ∀ r : ℝ, 0 < r → Continuous (fun σ : ℝ => ∫ w in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f ((EuclideanSpace.equiv (Fin (P + 1)) ℝ).symm (Fin.cons σ (EuclideanSpace.equiv (Fin P) ℝ w))) * θ (x + r • w) ∂(μHE[m] : Measure (Eucl P)))`

## Sibling prerequisites

- `root.flat_iff_weak-a1.tangent_locality-a1.blowup_change_of_variables-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
