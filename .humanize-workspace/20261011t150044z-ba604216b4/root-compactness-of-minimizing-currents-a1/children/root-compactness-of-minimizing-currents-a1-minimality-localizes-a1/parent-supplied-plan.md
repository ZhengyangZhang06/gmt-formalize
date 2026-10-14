# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.minimality_localizes-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-minimality-localizes-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1`
- Child key: `minimality_localizes`
- Declaration: `Submission.cmc_massOn_le_of_le_near_support`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (S T : GeometricCurrentOn U n) (K W W' : Set (Euclid P)), IsOpen U → IsIntegerMultiplicity S → IsIntegerMultiplicity T → IsCompact K → (S - T).support ⊆ K → IsOpen W → IsOpen W' → K ⊆ W → W ⊆ W' → CompactlyContained W' U → T.massOn W ≤ S.massOn W → T.massOn W' ≤ S.massOn W'`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.vanish_off_support-a1`
- `root.compactness_of_minimizing_currents-a1.mass_equals_rep_measure-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
