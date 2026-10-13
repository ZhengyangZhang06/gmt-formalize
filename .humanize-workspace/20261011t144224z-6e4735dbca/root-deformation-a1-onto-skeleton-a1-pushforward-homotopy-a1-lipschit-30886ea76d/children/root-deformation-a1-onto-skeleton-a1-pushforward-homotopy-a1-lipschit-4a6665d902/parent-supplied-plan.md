# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.current_criterion-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-lipschit-4a6665d902/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1`
- Child key: `current_criterion`
- Declaration: `Submission.dph_lpf_current_of_bounded_functional`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Eucl P)) (T₀ : TestFormOn U n → ℝ) (B : ℝ), (∀ ω η : TestFormOn U n, T₀ (ω + η) = T₀ ω + T₀ η) → (∀ (c : ℝ) (ω : TestFormOn U n), T₀ (c • ω) = c * T₀ ω) → (∀ (ω : TestFormOn U n) (C : ℝ), (∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) n) y) ≤ C) → |T₀ ω| ≤ B * C) → ∃ S : GeometricCurrentOn U n, (∀ ω, S ω = T₀ ω) ∧ S.mass ≤ ENNReal.ofReal B`

## Sibling prerequisites

- `root.flat_iff_weak-a1.im_series-a1.series_current-a1.continuity_criterion-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
