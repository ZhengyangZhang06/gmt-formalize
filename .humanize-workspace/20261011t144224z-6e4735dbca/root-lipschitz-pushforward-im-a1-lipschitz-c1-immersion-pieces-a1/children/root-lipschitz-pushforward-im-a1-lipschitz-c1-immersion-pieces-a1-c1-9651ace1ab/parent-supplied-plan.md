# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1.c1_approximation_eucl-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-lipschitz-c1-immersion-pieces-a1-c1-9651ace1ab/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1`
- Child key: `c1_approximation_eucl`
- Declaration: `Submission.lpf_c1_approximation_eucl`
- Exact Lean type: `∀ (n Q : ℕ) (u : Eucl n → Eucl Q) (K : ℝ≥0), LipschitzWith K u → ∀ ε : ℝ≥0∞, 0 < ε → ∃ (A : Set (Eucl n)) (G : Eucl n → Eucl Q), IsClosed A ∧ (volume : Measure (Eucl n)) Aᶜ < ε ∧ ContDiff ℝ 1 G ∧ ∀ x ∈ A, u x = G x ∧ HasFDerivAt u (fderiv ℝ G x) x`

## Sibling prerequisites

- `root.lipschitz_pushforward_im-a1.lipschitz_c1_immersion_pieces-a1.c1_approximation_real-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
