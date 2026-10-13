# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.polyhedral_im-a1.finite_piece_imrep-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-d892dc0ddc/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.polyhedral_im-a1`
- Child key: `finite_piece_imrep`
- Declaration: `Submission.cmcdtfrpi_finite_piece_imrep`
- Exact Lean type: `∀ (P k : ℕ) (I : Type) (U : Set (Euclid P)) (S : Finset I) (F : I → Set (Euclid P)) (m : I → ℕ) (ξ : I → MultiVector P k) (G : I → Euclid k → Euclid P), (∀ p ∈ S, MeasurableSet (F p)) → (∀ p ∈ S, F p ⊆ U) → (∀ p ∈ S, μHE[k] (F p) ≠ ∞) → (∀ p ∈ S, ∀ q ∈ S, p ≠ q → Disjoint (F p) (F q)) → (∀ p ∈ S, 0 < m p) → (∀ p ∈ S, ∃ K : NNReal, LipschitzWith K (G p)) → (∀ p ∈ S, F p ⊆ range (G p)) → (∀ p ∈ S, ∀ x ∈ F p, ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt k (⋃ q ∈ S, F q) x Q ∧ IsUnitOrientationOf (ξ p) Q) → ∃ R : IMRep U k, (∀ ω : TestFormOn U k, R.action (ω : DifferentialForm (Euclid P) k) = ∑ p ∈ S, (m p : ℝ) * ∫ x in F p, ξ p ((ω : DifferentialForm (Euclid P) k) x) ∂μHE[k]) ∧ R.measure univ = ∑ p ∈ S, (m p : ℝ≥0∞) * μHE[k] (F p)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
