# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1.pushforward_enorm_aemeasurable-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1-pushforw-aeac6d58da/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1`
- Child key: `pushforward_enorm_aemeasurable`
- Declaration: `Submission.lpf_raf_pushforward_enorm_aemeasurable`
- Exact Lean type: `∀ (P Q n : ℕ) (μ : Measure (Eucl P)) (L : Eucl P → (Eucl P →L[ℝ] Eucl Q)) (ξ : Eucl P → NVector (Eucl P) n), AEStronglyMeasurable L μ → AEStronglyMeasurable ξ μ → AEMeasurable (fun x => ‖nVectorPushforward n (L x) (ξ x)‖ₑ) μ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
