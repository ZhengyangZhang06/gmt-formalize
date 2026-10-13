# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.rectifiability-a1.projection_null-a1.pullback_top_form_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-projection-null-a1-pullback-top-form-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.rectifiability-a1.projection_null-a1`
- Child key: `pullback_top_form_bound`
- Declaration: `Submission.rpn_pullback_top_form_bound`
- Exact Lean type: `∀ (P m : ℕ) (U W : Set (Eucl P)) (T : GeometricCurrentOn U (m + 1)), W ⊆ U → T.massOn W < ∞ → T.boundary.massOn W < ∞ → ∀ f : Eucl P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → HasCompactSupport f → tsupport f ⊆ W → ∀ L : Eucl P →L[ℝ] Eucl (m + 1), ∃ C : ℝ, ∀ a : Eucl (m + 1) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a → HasCompactSupport a → ∀ M : ℝ, (∀ y, |a y| ≤ M) → ∀ φ : TestFormOn U (m + 1), (∀ x, (φ : DifferentialForm (Eucl P) (m + 1)) x = (f x * a (L x)) • wedgeCovectors (m + 1) (fun i => (EuclideanSpace.proj i : Eucl (m + 1) →L[ℝ] ℝ).comp L)) → |T φ| ≤ C * M * ((volume (tsupport a)).toReal) ^ ((1 : ℝ) / ((m : ℝ) + 1))`

## Sibling prerequisites

- `root.rectifiability-a1.projection_null-a1.potential_estimate-a1`
- `root.rectifiability-a1.projection_null-a1.potential_form_derivative-a1`
- `root.rectifiability-a1.projection_null-a1.mass_bound_opnorm-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
