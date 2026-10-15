# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.face_replacement-a1.boundary_variation-a1.face_test_form-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-6ba7d20c0f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.face_replacement-a1.boundary_variation-a1`
- Child key: `face_test_form`
- Declaration: `Submission.dimred_mbl_dtfrbv_face_test_form`
- Exact Lean type: `∀ (P m : ℕ) (p : (Fin (m + 1) → Fin P) × (Fin P → ℤ)) (N : Set (Euclid P)) (g : Euclid (m + 1) → Euclid (m + 1)), StrictMono p.1 → IsOpen N → (∀ y : Euclid (m + 1), (∀ i, 0 < y i ∧ y i < 1) → (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) ∈ N) → ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∃ γ : TestFormOn (univ : Set (Euclid P)) m, tsupport (γ : DifferentialForm (Euclid P) m) ⊆ N ∧ (∀ x, covectorEuclideanNorm ((γ : DifferentialForm (Euclid P) m) x) ≤ 1) ∧ ∀ (y : Euclid (m + 1)) (i : Fin (m + 1)), g y i = (-1 : ℝ) ^ (i : ℕ) * (γ : DifferentialForm (Euclid P) m) (WithLp.toLp 2 (fun k => (p.2 k : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun l => EuclideanSpace.single (p.1 (Fin.succAbove i l)) (1 : ℝ))`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.boundary_variation-a1.face_covectors-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
