# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.radon_compactness-a1.rc_cc_countable_dense-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/nodes/root-radon-compactness-a1-rc-cc-countable-dense-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.radon_compactness-a1`
- Child key: `rc_cc_countable_dense`
- Declaration: `Submission.rc_cc_countable_dense`
- Exact Lean type: `∀ (X : Type u) [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] (K : Set X), IsCompact K → ∃ D : Set C_c(X, ℝ), D.Countable ∧ (∀ g ∈ D, tsupport g ⊆ K) ∧ ∀ f : C_c(X, ℝ), tsupport f ⊆ K → ∀ ε : ℝ, 0 < ε → ∃ g ∈ D, ∀ x, |f x - g x| ≤ ε`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
