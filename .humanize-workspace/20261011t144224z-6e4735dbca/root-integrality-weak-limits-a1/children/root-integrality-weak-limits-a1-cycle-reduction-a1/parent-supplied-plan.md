# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.cycle_reduction-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1`
- Child key: `cycle_reduction`
- Declaration: `Submission.iwl_cycle_reduction`
- Exact Lean type: `∀ (P m : ℕ), LipschitzPushforwardIntegerMultiplicity → (∀ (Yj : ℕ → GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)) (Y : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)), (∀ j, IsIntegerMultiplicity (Yj j).boundary) → (⨆ j, (Yj j).boundary.mass) < ∞ → WeaklyConvergesOn (fun j => (Yj j).boundary) Y.boundary → IsIntegerMultiplicity Y.boundary) → (∀ (K : Set (Eucl P)), IsCompact K → ∀ (Tj : ℕ → GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)) (T : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)), (∀ j, IsIntegerMultiplicity (Tj j)) → (∀ j, (Tj j).boundary = 0) → (∀ j, (Tj j).support ⊆ K) → (⨆ j, (Tj j).mass) < ∞ → WeaklyConvergesOn Tj T → IsIntegerMultiplicity T) → (∀ (K : Set (Eucl P)), IsCompact K → ∀ (Tj : ℕ → GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)) (T : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)), (∀ j, IsIntegralCurrent (Tj j)) → (∀ j, (Tj j).support ⊆ K) → (⨆ j, ((Tj j).mass + (Tj j).boundary.mass)) < ∞ → WeaklyConvergesOn Tj T → IsIntegerMultiplicity T)`

## Sibling prerequisites

- `root.integrality_weak_limits-a1.im_closure-a1`
- `root.integrality_weak_limits-a1.smooth_pushforward-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
