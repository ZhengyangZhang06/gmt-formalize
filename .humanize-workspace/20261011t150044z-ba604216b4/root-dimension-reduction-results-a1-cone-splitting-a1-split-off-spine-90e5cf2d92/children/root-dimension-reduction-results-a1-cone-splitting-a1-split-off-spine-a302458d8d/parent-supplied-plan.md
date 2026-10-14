# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.cube_stokes-a1.frame_box_ftc-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-a302458d8d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.cube_stokes-a1`
- Child key: `frame_box_ftc`
- Declaration: `Submission.dimred_cs_sos_mt_cs_frame_box_ftc`
- Exact Lean type: `∀ (P j : ℕ) (g : Fin (j + 1) → Euclid P) (a : Fin (j + 1)) (r : ℝ) (A b : Euclid P → ℝ), Orthonormal ℝ g → 0 < r → Continuous A → Continuous b → (∀ (s : Euclid P) (τ : ℝ), HasDerivAt (fun σ : ℝ => b (s + σ • g a)) (A (s + τ • g a)) τ) → ∫ t in {t | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| ≤ r}, A t ∂μHE[j + 1] = (∫ s in {s | s ∈ Submodule.span ℝ (Set.range (g ∘ a.succAbove)) ∧ ∀ c, |inner ℝ (g (a.succAbove c)) s| ≤ r}, b (s + r • g a) ∂μHE[j]) - ∫ s in {s | s ∈ Submodule.span ℝ (Set.range (g ∘ a.succAbove)) ∧ ∀ c, |inner ℝ (g (a.succAbove c)) s| ≤ r}, b (s - r • g a) ∂μHE[j]`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.cube_stokes-a1.frame_box_integral-a1`
- `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.cube_stokes-a1.coord_box_ftc-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
