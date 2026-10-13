# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1.constant_limit-a1.mass_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-ded8027801/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1.constant_limit-a1`
- Child key: `mass_bound`
- Declaration: `Submission.cbr_ci_bl_cvl_massOn_le`
- Exact Lean type: `∀ (P n : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) n) (ν' : Measure (Euclid P)) (τ : Euclid P → MultiVector P n) (ζ₀ : MultiVector P n) (s B R : ℝ) (G : Set (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → ν' K < ∞) → AEStronglyMeasurable τ ν' → 0 ≤ s → (∀ α : Covector (Euclid P) n, |ζ₀ α| ≤ s * covectorEuclideanNorm α) → 0 ≤ B → (∀ α : Covector (Euclid P) n, ‖α‖ ≤ B * covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, X ω = ∫ x, τ x ((ω : DifferentialForm (Euclid P) n) x) ∂ν') → IsOpen G → G ⊆ closedBall (0 : Euclid P) R → X.massOn G ≤ ENNReal.ofReal s * ν' G + ENNReal.ofReal B * ∫⁻ x in closedBall (0 : Euclid P) R, ‖τ x - ζ₀‖ₑ ∂ν'`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1.constant_limit-a1.pairing_error-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
