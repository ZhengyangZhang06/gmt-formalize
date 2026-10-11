# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.variation_formulas-a1.jacobian_family-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-variation-formulas-a1-jacobian-family-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.variation_formulas-a1`
- Child key: `jacobian_family`
- Declaration: `Submission.variation_jacobian_family`
- Exact Lean type: `∀ (N : ℕ) (U K : Set (Rn N)) (φ : ℝ → Rn N → Rn N), let g : ℝ × (Rn N × (Rn N →L[ℝ] Rn N)) → ℝ := fun p ↦ Real.sqrt ((1 - p.2.2 + p.2.2 ∘L ContinuousLinearMap.adjoint (fderiv ℝ (φ p.1) p.2.1) ∘L fderiv ℝ (φ p.1) p.2.1 ∘L p.2.2).det); (IsAdmissibleDeformation 2 U K φ → (∀ x ∈ U, ∀ P : Rn N →L[ℝ] Rn N, P ∘L P = P → ContDiffAt ℝ 1 g (0, (x, P))) ∧ ∀ (M : Set (Rn N)) (y : Rn N), y ∈ U → HasDerivAt (fun t ↦ g (t, (y, tangentProjection M y))) (tangentialDivergence M (initialVelocity φ) y) 0) ∧ (IsAdmissibleDeformation 3 U K φ → (∀ x ∈ U, ∀ P : Rn N →L[ℝ] Rn N, P ∘L P = P → ContDiffAt ℝ 2 g (0, (x, P))) ∧ ∀ (M : Set (Rn N)) (y : Rn N), y ∈ U → HasDerivAt (fun t ↦ deriv (fun s ↦ g (s, (y, tangentProjection M y))) t) (secondVariationIntegrand M φ y) 0) ∧ ∀ r : ℕ∞, IsAdmissibleDeformation r U K φ → ∀ (M : Set (Rn N)) (y : Rn N), y ∉ K → tangentialDivergence M (initialVelocity φ) y = 0 ∧ secondVariationIntegrand M φ y = 0`

## Sibling prerequisites

- `root.variation_formulas-a1.gram_det_derivatives-a1`
- `root.variation_formulas-a1.deformation_calculus-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
