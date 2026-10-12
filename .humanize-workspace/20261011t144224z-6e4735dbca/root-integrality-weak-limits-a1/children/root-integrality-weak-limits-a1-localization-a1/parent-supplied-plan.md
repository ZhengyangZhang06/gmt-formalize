# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.localization-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-localization-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1`
- Child key: `localization`
- Declaration: `Submission.iwl_localization`
- Exact Lean type: `∀ (P m : ℕ), SlicingTheorem → (∀ (K : Set (Eucl P)), IsCompact K → ∀ (Tj : ℕ → GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)) (T : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)), (∀ j, IsIntegralCurrent (Tj j)) → (∀ j, (Tj j).support ⊆ K) → (⨆ j, ((Tj j).mass + (Tj j).boundary.mass)) < ∞ → WeaklyConvergesOn Tj T → IsIntegerMultiplicity T) → (∀ (U : Set (Eucl P)), IsOpen U → ∀ (Tj : ℕ → GeometricCurrentOn U (m + 1)) (T : GeometricCurrentOn U (m + 1)), (∀ j, IsIntegralCurrent (Tj j)) → (∀ W, CompactlyContainedOpen W U → (⨆ j, ((Tj j).massOn W + (Tj j).boundary.massOn W)) < ∞) → WeaklyConvergesOn Tj T → IsIntegerMultiplicity T)`

## Sibling prerequisites

- `root.integrality_weak_limits-a1.tangent_locality-a1`
- `root.integrality_weak_limits-a1.patching-a1`
- `root.integrality_weak_limits-a1.restriction_theory-a1`
- `root.integrality_weak_limits-a1.im_closure-a1`
- `root.integrality_weak_limits-a1.restriction_limit-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
