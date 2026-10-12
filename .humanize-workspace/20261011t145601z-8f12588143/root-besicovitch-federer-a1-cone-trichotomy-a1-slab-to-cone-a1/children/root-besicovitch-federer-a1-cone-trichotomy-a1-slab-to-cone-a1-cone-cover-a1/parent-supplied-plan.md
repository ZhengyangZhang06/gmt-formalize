# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.besicovitch_federer-a1.cone_trichotomy-a1.slab_to_cone-a1.cone_cover-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-besicovitch-federer-a1-cone-trichotomy-a1-slab-to-cone-a1-cone-cover-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.besicovitch_federer-a1.cone_trichotomy-a1.slab_to_cone-a1`
- Child key: `cone_cover`
- Declaration: `Submission.bf_cone_subset_iUnion_slabCones`
- Exact Lean type: `∀ (n ℓ : ℕ), 0 < ℓ → ∀ W : Submodule ℝ (Rn (n + ℓ)), finrank ℝ W = n → ∀ u : Fin ℓ → Rn (n + ℓ), Orthonormal ℝ u → (∀ j, u j ∈ Wᗮ) → ∀ (y : Rn (n + ℓ)) (s : ℝ), ‖W.starProjection y‖ < s * ‖y‖ → ∃ j, ‖W.starProjection y‖ < Real.sqrt (ℓ : ℝ) * s * ‖W.starProjection y + inner ℝ y (u j) • u j‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
