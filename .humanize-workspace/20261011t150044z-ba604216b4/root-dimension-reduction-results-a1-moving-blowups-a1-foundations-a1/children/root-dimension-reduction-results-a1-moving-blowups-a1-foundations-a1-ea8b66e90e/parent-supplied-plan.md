# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.foundations-a1.divergence_form-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-foundations-a1-ea8b66e90e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.foundations-a1`
- Child key: `divergence_form`
- Declaration: `Submission.dimred_mbl_fnd_coordinate_divergence_form`
- Exact Lean type: `∀ (P m : ℕ) (I : Fin (m + 1) → Fin P) (θ : Covector (Euclid P) (m + 1)) (b : Euclid P → ℝ), StrictMono I → (∀ v : Fin (m + 1) → Euclid P, θ v = Matrix.det (Matrix.of fun k j => v j (I k))) → ContDiff ℝ (⊤ : ℕ∞) b → HasCompactSupport b → ∃ K : ℝ, ∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g → (∀ y, ‖g y‖ ≤ 1) → ∃ (η : DifferentialForm (Euclid P) m) (ζ : DifferentialForm (Euclid P) (m + 1)), IsTestForm η ∧ IsTestForm ζ ∧ tsupport η ⊆ tsupport b ∧ tsupport ζ ⊆ tsupport b ∧ (∀ x, covectorEuclideanNorm (η x) ≤ K) ∧ (∀ x, covectorEuclideanNorm (ζ x) ≤ K) ∧ ∀ x, exteriorDerivative η x = (b x * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g (WithLp.toLp 2 (fun k => x (I k)))).toLinearMap) • θ + ζ x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
