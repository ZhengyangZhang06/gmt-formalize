# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1.lipschitz_localization-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1-lip-66ca1b75a5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1`
- Child key: `lipschitz_localization`
- Declaration: `Submission.lpf_lipschitz_localization`
- Exact Lean type: `∀ (n Q : ℕ) (Ω : Set (Eucl n)) (u : Eucl n → Eucl Q), IsOpen Ω → LocallyLipschitzOn Ω u → ∃ (B : ℕ → Set (Eucl n)) (v : ℕ → Eucl n → Eucl Q), (∀ m, IsOpen (B m)) ∧ (∀ m, B m ⊆ Ω) ∧ Ω ⊆ ⋃ m, B m ∧ (∀ m, ∃ K : ℝ≥0, LipschitzWith K (v m)) ∧ ∀ m, EqOn u (v m) (B m)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
