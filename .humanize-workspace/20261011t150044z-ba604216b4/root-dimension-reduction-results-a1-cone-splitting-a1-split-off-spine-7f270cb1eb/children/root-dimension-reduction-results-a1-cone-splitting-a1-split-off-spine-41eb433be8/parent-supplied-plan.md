# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.frame_measure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-41eb433be8/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1`
- Child key: `frame_measure`
- Declaration: `Submission.dimred_cs_sos_mt_frame_measure`
- Exact Lean type: `∀ (P k : ℕ) (g : Fin k → Euclid P), Orthonormal ℝ g → (volume : Measure (Fin k → ℝ)).map (fun u => ∑ i, u i • g i) = μHE[k].restrict (Submodule.span ℝ (Set.range g) : Set (Euclid P)) ∧ ∀ r : ℝ, 0 < r → μHE[k] {t | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| ≤ r} = ENNReal.ofReal ((2 * r) ^ k) ∧ μHE[k] {t | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| < r} = ENNReal.ofReal ((2 * r) ^ k)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
