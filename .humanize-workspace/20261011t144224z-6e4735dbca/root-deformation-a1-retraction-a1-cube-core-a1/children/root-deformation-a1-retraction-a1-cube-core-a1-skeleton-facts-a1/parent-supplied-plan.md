# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.retraction-a1.cube_core-a1.skeleton_facts-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-retraction-a1-cube-core-a1-skeleton-facts-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.retraction-a1.cube_core-a1`
- Child key: `skeleton_facts`
- Declaration: `Submission.dr_cc_skeleton_facts`
- Exact Lean type: `∀ (m ℓ : ℕ) (a : Eucl (m + 1 + ℓ)), (∀ i, 1 / 4 < a i ∧ a i < 3 / 4) → ∀ La : Set (Eucl (m + 1 + ℓ)), La = {y | ∃ J : Finset (Fin (m + 1 + ℓ)), J.card = m + 2 ∧ ∀ i ∈ J, ∃ k : ℤ, y i - a i = k} → IsClosed La ∧ (∀ (J : Finset (Fin (m + 1 + ℓ))) (c : Eucl (m + 1 + ℓ)), m + 2 ≤ J.card → (∀ i ∈ J, c i = a i) → c ∈ La) ∧ ∀ (J : Finset (Fin (m + 1 + ℓ))) (c x y : Eucl (m + 1 + ℓ)) (s : ℝ), (∀ i ∈ J, c i = a i) → (∀ i ∉ J, c i = 0 ∨ c i = 1) → (∀ i ∉ J, x i = c i) → (∀ i, 0 ≤ y i ∧ y i ≤ 1) → 0 < s → (∀ i, y i - c i = s * (x i - c i)) → y ∈ La → x ∈ La`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
