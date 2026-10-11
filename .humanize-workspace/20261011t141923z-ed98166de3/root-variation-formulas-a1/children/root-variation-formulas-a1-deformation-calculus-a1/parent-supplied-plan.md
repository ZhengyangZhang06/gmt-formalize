# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.variation_formulas-a1.deformation_calculus-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-variation-formulas-a1-deformation-calculus-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.variation_formulas-a1`
- Child key: `deformation_calculus`
- Declaration: `Submission.variation_deformation_calculus`
- Exact Lean type: `∀ (N : ℕ) (U K : Set (Rn N)) (φ : ℝ → Rn N → Rn N), (∀ r : ℕ∞, IsAdmissibleDeformation r U K φ → ∀ x, x ∉ K → initialVelocity φ x = 0 ∧ initialAcceleration φ x = 0 ∧ fderiv ℝ (initialVelocity φ) x = 0 ∧ fderiv ℝ (initialAcceleration φ) x = 0) ∧ (IsAdmissibleDeformation 2 U K φ → (∀ t ∈ Ioo (-1 : ℝ) 1, ∀ x ∈ U, ContDiffAt ℝ 1 (fun p : ℝ × Rn N ↦ fderiv ℝ (φ p.1) p.2) (t, x)) ∧ ∀ y ∈ U, fderiv ℝ (φ 0) y = 1 ∧ HasDerivAt (fun t ↦ fderiv ℝ (φ t) y) (fderiv ℝ (initialVelocity φ) y) 0) ∧ (IsAdmissibleDeformation 3 U K φ → (∀ t ∈ Ioo (-1 : ℝ) 1, ∀ x ∈ U, ContDiffAt ℝ 2 (fun p : ℝ × Rn N ↦ fderiv ℝ (φ p.1) p.2) (t, x)) ∧ ∀ y ∈ U, (∀ᶠ t in 𝓝 0, DifferentiableAt ℝ (fun s ↦ fderiv ℝ (φ s) y) t) ∧ HasDerivAt (deriv (fun s ↦ fderiv ℝ (φ s) y)) (fderiv ℝ (initialAcceleration φ) y) 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
