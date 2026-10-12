# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.coarea_and_slices-a1.c1_level_slices_rectifiable-a1.null_image-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-coarea-and-slices-a1-c1-level-slices-rectifiable-a1-null-image-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.coarea_and_slices-a1.c1_level_slices_rectifiable-a1`
- Child key: `null_image`
- Declaration: `Submission.contDiffOn_image_euclideanHausdorff_null`
- Exact Lean type: `∀ (n N k : ℕ) (D Z : Set (Rn n)) (ψ : Rn n → Rn N), IsOpen D → ContDiffOn ℝ 1 ψ D → Z ⊆ D → μHE[k] Z = 0 → μHE[k] (ψ '' Z) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
