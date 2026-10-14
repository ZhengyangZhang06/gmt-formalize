# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.localize-a1.mass_agree-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-localize-a1-mass-agree-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.localize-a1`
- Child key: `mass_agree`
- Declaration: `Submission.dtc_massOn_eq_of_agreeOn`
- Exact Lean type: `∀ (P n : ℕ) (U V W : Set (Euclid P)) (hVU : V ⊆ U) (S : GeometricCurrentOn U n) (S' : GeometricCurrentOn V n), W ⊆ V → (∀ ω : TestFormOn V n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ W → S (testFormOnInclusion hVU n ω) = S' ω) → S.massOn W = S'.massOn W`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
