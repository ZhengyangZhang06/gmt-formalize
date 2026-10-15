# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.face_integral_current-a1.divergence_field-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-c5035a4b1c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.face_integral_current-a1`
- Child key: `divergence_field`
- Declaration: `Submission.cmcdtfrfic_divergence_field`
- Exact Lean type: `∀ (P m : ℕ) (γ : DifferentialForm (Euclid P) m) (ι : Fin (m + 1) → Fin P) (a : Euclid P), ContDiff ℝ (⊤ : ℕ∞) γ → StrictMono ι → ∃ G : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) G ∧ (∀ y, ‖G y‖ ≤ covectorEuclideanNorm (γ (a + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)))) ∧ ∀ y, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y) = exteriorDerivative γ (a + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) (fun j => EuclideanSpace.single (ι j) (1 : ℝ))`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.face_integral_current-a1.coeff_bounds-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
