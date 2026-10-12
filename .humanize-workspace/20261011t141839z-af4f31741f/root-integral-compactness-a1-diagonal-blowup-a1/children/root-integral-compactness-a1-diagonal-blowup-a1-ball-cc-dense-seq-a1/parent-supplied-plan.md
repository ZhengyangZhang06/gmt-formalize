# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.diagonal_blowup-a1.ball_cc_dense_seq-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-diagonal-blowup-a1-ball-cc-dense-seq-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.diagonal_blowup-a1`
- Child key: `ball_cc_dense_seq`
- Declaration: `Submission.intcpt_diag_ball_cc_dense_seq`
- Exact Lean type: `∀ (N n : ℕ) (R : ℝ), 0 < R → ∃ g : ℕ → C_c(Euclidean N × Grassmannian N n, ℝ), (∀ m, tsupport (g m) ⊆ ball (0 : Euclidean N) R ×ˢ (univ : Set (Grassmannian N n))) ∧ ∀ f : C_c(Euclidean N × Grassmannian N n, ℝ), tsupport f ⊆ ball (0 : Euclidean N) R ×ˢ (univ : Set (Grassmannian N n)) → ∀ η : ℝ, 0 < η → ∃ m, ∀ z, |f z - g m z| ≤ η`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
