# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.weak_limit_mass_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-c658ab2df9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1`
- Child key: `weak_limit_mass_bound`
- Declaration: `Submission.idtp_convergesWeakly_massOn_le`
- Exact Lean type: `∀ (P n : ℕ) (Us : ℕ → Set (Euclid P)) (V : Set (Euclid P)) (Ts : (j : ℕ) → GeometricCurrentOn (Us j) n) (S : GeometricCurrentOn V n) (W : Set (Euclid P)) (B : ℝ≥0∞), ConvergesWeakly Ts S → (∀ᶠ j in atTop, W ⊆ Us j ∧ (Ts j).massOn W ≤ B) → S.massOn W ≤ B`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
