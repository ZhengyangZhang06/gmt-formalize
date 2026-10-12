# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.coarea_formula-a1.critical_fibers_euclidean-a1.compact_small_covers-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-coarea-formula-a1-critical-fibers-euclidean-a1-compact-small-covers-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.coarea_formula-a1.critical_fibers_euclidean-a1`
- Child key: `compact_small_covers`
- Declaration: `Submission.critical_set_small_ball_covers_of_isCompact`
- Exact Lean type: `∀ (m k : ℕ) (V Q : Set (Rn (m + k))) (G : Rn (m + k) → Rn m), IsOpen V → ContDiffOn ℝ 1 G V → IsCompact Q → Q ⊆ V → ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∃ (s : Finset (Rn (m + k))) (r : ℝ), 0 < r ∧ 2 * r ≤ δ ∧ {x | x ∈ Q ∧ ¬ Function.Surjective (fderiv ℝ G x)} ⊆ ⋃ x ∈ s, closedBall x r ∧ ∑ x ∈ s, ENNReal.ofReal ((2 * r) ^ k) * volume (G '' closedBall x r) ≤ ENNReal.ofReal ε`

## Sibling prerequisites

- `root.coarea_formula-a1.critical_fibers_euclidean-a1.ball_image_volume-a1`
- `root.coarea_formula-a1.critical_fibers_euclidean-a1.ball_cover_count-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
