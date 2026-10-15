# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1.limsup_thickening-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-65bd1b3ecb/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1`
- Child key: `limsup_thickening`
- Declaration: `Submission.dmcbr_ci_bl_limsup_le_of_cthickening`
- Exact Lean type: `∀ (P : ℕ) (a : ℕ → ℝ≥0∞) (νs : ℕ → Measure (Euclid P)) (ν : Measure (Euclid P)) (c : ℝ≥0∞) (K : Set (Euclid P)), IsCompact K → c ≠ ∞ → (∀ K' : Set (Euclid P), IsCompact K' → ν K' < ∞) → (∀ K' : Set (Euclid P), IsCompact K' → limsup (fun k => νs k K') atTop ≤ ν K') → (∀ r : ℝ, 0 < r → ∃ v : ℕ → ℝ≥0∞, Tendsto v atTop (𝓝 0) ∧ ∀ k, a k ≤ c * νs k (cthickening r K) + v k) → limsup a atTop ≤ c * ν K`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
