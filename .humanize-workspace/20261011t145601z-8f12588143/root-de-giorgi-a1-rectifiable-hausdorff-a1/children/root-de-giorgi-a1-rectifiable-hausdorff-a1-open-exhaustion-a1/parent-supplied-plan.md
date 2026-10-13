# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.rectifiable_hausdorff-a1.open_exhaustion-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-rectifiable-hausdorff-a1-open-exhaustion-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.rectifiable_hausdorff-a1`
- Child key: `open_exhaustion`
- Declaration: `Submission.deGiorgiRH_open_exhaustion`
- Exact Lean type: `∀ (N : ℕ) (U : Set (Rn N)), IsOpen U → ∃ W : ℕ → Set (Rn N), (∀ i, IsOpen (W i) ∧ IsCompact (closure (W i)) ∧ closure (W i) ⊆ U) ∧ ⋃ i, W i = U`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
