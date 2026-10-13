# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1.local_lipschitz_area-a1.disjoint_lipschitz_pieces-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-rectifiable-area-formula-a1-local-li-1721d1b1cf/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_pushforward_im-a1.rectifiable_area_formula-a1.local_lipschitz_area-a1`
- Child key: `disjoint_lipschitz_pieces`
- Declaration: `Submission.lpf_raf_lla_disjoint_lipschitz_pieces`
- Exact Lean type: `∀ (n Q : ℕ) (Ω D : Set (Eucl n)) (u : Eucl n → Eucl Q), IsOpen Ω → LocallyLipschitzOn Ω u → D ⊆ Ω → NullMeasurableSet D (volume : Measure (Eucl n)) → ∃ (V B : ℕ → Set (Eucl n)) (K : ℕ → ℝ≥0), (∀ m, IsOpen (V m)) ∧ (∀ m, V m ⊆ Ω) ∧ (∀ m, LipschitzOnWith (K m) u (V m)) ∧ (∀ m, B m ⊆ D ∩ V m) ∧ Pairwise (Function.onFun Disjoint B) ∧ (∀ m, NullMeasurableSet (B m) (volume : Measure (Eucl n))) ∧ D ⊆ ⋃ m, B m`

## Sibling prerequisites

- `root.lipschitz_pushforward_im-a1.locally_lipschitz_image-a1.countable_lipschitz_cover-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
