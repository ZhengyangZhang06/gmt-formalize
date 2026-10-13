# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_approx-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-approx-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1`
- Child key: `smooth_approx`
- Declaration: `Submission.dph_lipschitz_smooth_approx`
- Exact Lean type: `∀ (m m' : ℕ) (G : Eucl m → Eucl m') (Λ : ℝ≥0) (A : Set (Eucl m)) (δ : ℝ), 0 < δ → LipschitzOnWith Λ G (thickening δ A) → ∃ (G' : Eucl m → Eucl m') (Gj : ℕ → Eucl m → Eucl m') (L : ℝ≥0), LipschitzWith L G' ∧ EqOn G' G (thickening δ A) ∧ (∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj j)) ∧ (∀ j, LipschitzWith L (Gj j)) ∧ TendstoUniformly Gj G' atTop ∧ (∀ j, ∀ x ∈ thickening (δ / 2) A, ‖fderiv ℝ (Gj j) x‖ ≤ Λ) ∧ ∀ (k : ℕ) (α : SimonMultiIndex k m') (z : Eucl m') (ω : TestFormOn (univ : Set (Eucl m')) k) (ε : ℝ), 0 < ε → (∀ x ∈ thickening ε A, G x ∈ thickening ε (tsupport (ω : DifferentialForm (Eucl m') k)) → ∀ i, i ∉ range α → G x i = z i) → (∀ y, (ω : DifferentialForm (Eucl m') k) y (fun j => EuclideanSpace.single (α j) (1 : ℝ)) = 0) → ∃ r : ℝ, 0 < r ∧ ∀ᶠ j in atTop, ∀ x ∈ thickening r A, ((ω : DifferentialForm (Eucl m') k) (Gj j x)).compContinuousLinearMap (fderiv ℝ (Gj j) x) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
