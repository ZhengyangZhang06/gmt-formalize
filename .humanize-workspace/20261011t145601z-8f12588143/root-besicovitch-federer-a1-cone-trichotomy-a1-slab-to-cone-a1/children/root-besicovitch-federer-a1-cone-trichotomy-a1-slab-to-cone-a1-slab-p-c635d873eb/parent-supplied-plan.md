# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.besicovitch_federer-a1.cone_trichotomy-a1.slab_to_cone-a1.slab_projection-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-besicovitch-federer-a1-cone-trichotomy-a1-slab-to-cone-a1-slab-p-c635d873eb/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.besicovitch_federer-a1.cone_trichotomy-a1.slab_to_cone-a1`
- Child key: `slab_projection`
- Declaration: `Submission.bf_starProjection_sup_span_unit`
- Exact Lean type: `∀ (N : ℕ) (W : Submodule ℝ (Rn N)) (u : Rn N), u ∈ Wᗮ → ‖u‖ = 1 → ∀ y : Rn N, (W ⊔ Submodule.span ℝ {u}).starProjection y = W.starProjection y + inner ℝ y u • u`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
