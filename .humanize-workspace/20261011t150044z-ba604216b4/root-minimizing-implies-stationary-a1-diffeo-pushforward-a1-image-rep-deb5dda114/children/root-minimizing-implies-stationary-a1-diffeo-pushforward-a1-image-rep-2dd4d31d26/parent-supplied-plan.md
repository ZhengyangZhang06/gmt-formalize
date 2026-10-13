# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.image_representation-a1.image_imrep-a1.rectifiable_image-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-image-rep-2dd4d31d26/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.image_representation-a1.image_imrep-a1`
- Child key: `rectifiable_image`
- Declaration: `Submission.dpfir_ii_countablyRectifiable_image_of_lipschitz`
- Exact Lean type: `∀ (P n : ℕ) (M : Set (Euclid P)) (φ : Euclid P → Euclid P) (Λ : NNReal), LipschitzWith Λ φ → CountablyRectifiable n M → CountablyRectifiable n (φ '' M)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
