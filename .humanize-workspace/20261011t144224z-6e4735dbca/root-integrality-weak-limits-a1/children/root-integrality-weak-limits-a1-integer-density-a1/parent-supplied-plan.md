# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.integer_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1`
- Child key: `integer_density`
- Declaration: `Submission.iwl_integer_density`
- Exact Lean type: `∀ (P m : ℕ), m + 2 ≤ P → SlicingTheorem → LipschitzPushforwardIntegerMultiplicity → ∀ (Tj : ℕ → GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)) (T : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)), (∀ j, IsIntegerMultiplicity (Tj j)) → (∀ j, (Tj j).boundary = 0) → (⨆ j, (Tj j).mass) < ∞ → WeaklyConvergesOn Tj T → IsRectifiableCurrent T → IsIntegerMultiplicity T`

## Sibling prerequisites

- `root.integrality_weak_limits-a1.tangent_locality-a1`
- `root.integrality_weak_limits-a1.top_dim-a1`
- `root.integrality_weak_limits-a1.restriction_theory-a1`
- `root.integrality_weak_limits-a1.restriction_limit-a1`
- `root.integrality_weak_limits-a1.smooth_pushforward-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
