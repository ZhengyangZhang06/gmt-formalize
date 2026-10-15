# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.cube_stokes-a1.coord_box_ftc-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-f1e97b0495/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.cube_stokes-a1`
- Child key: `coord_box_ftc`
- Declaration: `Submission.dimred_cs_sos_mt_cs_coord_box_ftc`
- Exact Lean type: `∀ (j : ℕ) (a : Fin (j + 1)) (r : ℝ) (φ ψ : (Fin (j + 1) → ℝ) → ℝ), 0 < r → Continuous φ → (∀ (u : Fin j → ℝ) (τ : ℝ), HasDerivAt (fun σ : ℝ => ψ (Fin.insertNth a σ u)) (φ (Fin.insertNth a τ u)) τ) → ∫ u in {u : Fin (j + 1) → ℝ | ∀ i, |u i| ≤ r}, φ u = ∫ u in {u : Fin j → ℝ | ∀ c, |u c| ≤ r}, (ψ (Fin.insertNth a r u) - ψ (Fin.insertNth a (-r) u))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
