# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.decay_at_origin-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-decay-at-origin-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1`
- Child key: `decay_at_origin`
- Declaration: `Submission.ted_decay_at_origin`
- Exact Lean type: `TiltExcessHeightEstimate → AffineApproximationLemma → LipschitzApproximationLemma → HarmonicApproximationLemma → ∀ n ℓ : ℕ, 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 / 128 → ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ δ₁ → V.AllardHypotheses H p δ ρ → ∀ T : Submodule ℝ (Amb n ℓ), Module.finrank ℝ T = n → ∃ S : Submodule ℝ (Amb n ℓ), Module.finrank ℝ S = n ∧ V.tiltExcess 0 (t * (δ * ρ)) S ≤ C * t ^ 2 * V.tiltExcessStar H p δ 0 (δ * ρ) T`

## Sibling prerequisites

- `root.tilt_excess_decay-a1.allard_density_bounds-a1`
- `root.tilt_excess_decay-a1.tangent_plane_facts-a1`
- `root.tilt_excess_decay-a1.harmonic_affine_approx-a1`
- `root.tilt_excess_decay-a1.graph_weak_equation-a1`
- `root.tilt_excess_decay-a1.lemma_a_tilt_height-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
