# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.allard_lemma-a1.bad_set_bound-a1.marginal_measure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1-bad-set-bound-a1-margina-2792621399/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.allard_lemma-a1.bad_set_bound-a1`
- Child key: `marginal_measure`
- Declaration: `Submission.intcpt_allard_bsb_marginal_measure`
- Exact Lean type: `∀ (N n : ℕ) (m : Measure (Euclidean N × Grassmannian N n)) (g : Euclidean N × Grassmannian N n → ℝ≥0∞), ∃ τ : Measure (Euclidean N), ∀ A : Set (Euclidean N), MeasurableSet A → τ A = ∫⁻ z in A ×ˢ (univ : Set (Grassmannian N n)), g z ∂m`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
