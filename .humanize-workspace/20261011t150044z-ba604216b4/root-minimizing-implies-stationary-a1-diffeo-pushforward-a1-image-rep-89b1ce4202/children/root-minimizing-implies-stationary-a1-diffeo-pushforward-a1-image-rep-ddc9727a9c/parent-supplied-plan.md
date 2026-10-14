# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.image_representation-a1.area_integral_transfer-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-image-rep-ddc9727a9c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.image_representation-a1`
- Child key: `area_integral_transfer`
- Declaration: `Submission.dpfir_integral_eq_of_area_lintegral`
- Exact Lean type: `∀ (P : ℕ) (μ ν : Measure (Euclid P)) (φ : Euclid P → Euclid P) (J h f : Euclid P → ℝ), (∀ x, 0 ≤ J x) → (∀ g : Euclid P → ℝ≥0∞, ∫⁻ y, g y ∂ν = ∫⁻ x, ENNReal.ofReal (J x) * g (φ x) ∂μ) → AEStronglyMeasurable h ν → Integrable f μ → (∀ᵐ x ∂μ, J x * h (φ x) = f x) → Integrable h ν ∧ ∫ y, h y ∂ν = ∫ x, f x ∂μ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
