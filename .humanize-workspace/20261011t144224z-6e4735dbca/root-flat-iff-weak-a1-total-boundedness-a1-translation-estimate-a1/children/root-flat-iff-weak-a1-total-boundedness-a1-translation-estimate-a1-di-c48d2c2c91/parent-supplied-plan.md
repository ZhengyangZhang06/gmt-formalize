# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.total_boundedness-a1.translation_estimate-a1.directional_form-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1-translation-estimate-a1-di-c48d2c2c91/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1.total_boundedness-a1.translation_estimate-a1`
- Child key: `directional_form`
- Declaration: `Submission.fiw_tb_te_directional_form`
- Exact Lean type: `∀ (m : ℕ) (φ : Eucl (m + 1) → ℝ) (h : Eucl (m + 1)), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ → ∃ ω : TestFormOn (univ : Set (Eucl (m + 1))) m, (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Eucl (m + 1)) m) x) ≤ ‖h‖ * |φ x|) ∧ ∀ x, ((exteriorDerivativeTestOn (univ : Set (Eucl (m + 1))) m ω : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1)) : DifferentialForm (Eucl (m + 1)) (m + 1)) x (fun i => EuclideanSpace.single i (1 : ℝ)) = fderiv ℝ φ x h`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
