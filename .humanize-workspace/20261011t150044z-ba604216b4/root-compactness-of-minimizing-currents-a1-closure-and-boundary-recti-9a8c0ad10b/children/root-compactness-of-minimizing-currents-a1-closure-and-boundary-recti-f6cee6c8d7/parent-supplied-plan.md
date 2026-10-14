# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.im_local-a1.glue-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-f6cee6c8d7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.im_local-a1`
- Child key: `glue`
- Declaration: `Submission.cbr_isIntegerMultiplicity_of_local_reps`
- Exact Lean type: `(∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) → ∀ (P k : ℕ) (U : Set (Euclid P)) (X : GeometricCurrentOn U k) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P k), IsOpen U → μ Uᶜ = 0 → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ ω : TestFormOn U k, X ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ) → (∀ x ∈ U, ∃ (W : Set (Euclid P)) (R : IMRep W k), IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧ μ.restrict W = R.measure ∧ ∀ᵐ y ∂μ, y ∈ W → ξ y = R.orient y) → IsIntegerMultiplicity X`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.im_local-a1.imrep_measure-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
