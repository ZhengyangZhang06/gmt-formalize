# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.coarea_and_slices-a1.jacobian_identification-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-coarea-and-slices-a1-jacobian-identification-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.coarea_and_slices-a1`
- Child key: `jacobian_identification`
- Declaration: `Submission.chart_coarea_jacobian_identification`
- Exact Lean type: `∀ (n N m : ℕ) (M : Set (Rn N)) (θ : Rn N → ℝ) (f : Rn N → Rn m) (x : Rn N) (A : Rn n →L[ℝ] Rn N) (Γ : Rn n →L[ℝ] Rn m), θ x ≠ 0 → Function.Injective A → HasWeightedApproximateTangentSpaceAt n M θ x (LinearMap.range A.toLinearMap) → (∀ w : Rn n, HasLineDerivAt ℝ f (Γ w) x (A w)) → approxTangentPlane n M θ x = LinearMap.range A.toLinearMap ∧ (∃ L : ↥(LinearMap.range A.toLinearMap) →L[ℝ] Rn m, HasTangentialDifferentialAt (LinearMap.range A.toLinearMap) f x L) ∧ coareaJacobian (approxTangentPlane n M θ x) f x * A.toLinearMap.normDet = (A.toLinearMap ∘ₗ (LinearMap.ker Γ.toLinearMap).subtype).normDet * (LinearMap.adjoint Γ.toLinearMap).normDet`

## Sibling prerequisites

- `root.coarea_and_slices-a1.normdet_chain_rule-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
