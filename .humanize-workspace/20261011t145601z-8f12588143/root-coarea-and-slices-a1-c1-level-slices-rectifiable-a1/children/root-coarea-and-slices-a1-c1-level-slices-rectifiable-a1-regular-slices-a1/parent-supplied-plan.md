# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.coarea_and_slices-a1.c1_level_slices_rectifiable-a1.regular_slices-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-coarea-and-slices-a1-c1-level-slices-rectifiable-a1-regular-slices-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.coarea_and_slices-a1.c1_level_slices_rectifiable-a1`
- Child key: `regular_slices`
- Declaration: `Submission.c1_regular_level_slice_image_countablyRectifiable`
- Exact Lean type: `∀ (m k N : ℕ) (D : Set (Rn (m + k))) (ψ : Rn (m + k) → Rn N) (G : Rn (m + k) → Rn m) (y : Rn m), IsOpen D → ContDiffOn ℝ 1 ψ D → ContDiff ℝ 1 G → CountablyRectifiable k (ψ '' (D ∩ {u | Function.Surjective (fderiv ℝ G u)} ∩ G ⁻¹' {y}))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
