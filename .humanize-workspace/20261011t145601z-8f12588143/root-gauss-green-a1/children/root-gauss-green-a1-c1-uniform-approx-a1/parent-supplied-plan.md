# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.gauss_green-a1.c1_uniform_approx-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-gauss-green-a1-c1-uniform-approx-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.gauss_green-a1`
- Child key: `c1_uniform_approx`
- Declaration: `Submission.gaussGreenRep_c1_uniform_approx`
- Exact Lean type: `∀ (N : ℕ) (g : Rn N → Rn N) (W : Set (Rn N)), Continuous g → HasCompactSupport g → IsOpen W → tsupport g ⊆ W → ∃ K : Set (Rn N), IsCompact K ∧ tsupport g ⊆ K ∧ K ⊆ W ∧ ∃ h : ℕ → Rn N → Rn N, (∀ k, ContDiff ℝ 1 (h k) ∧ HasCompactSupport (h k) ∧ tsupport (h k) ⊆ K) ∧ TendstoUniformly h g atTop`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
