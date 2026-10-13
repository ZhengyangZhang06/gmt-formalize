# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_semicontinuity-a1.weight_portmanteau-a1.urysohn_sandwich-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-density-semicontinuity-a1-weight-portmanteau-a1-urysohn-sandwich-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_semicontinuity-a1.weight_portmanteau-a1`
- Child key: `urysohn_sandwich`
- Declaration: `Submission.exists_urysohn_integral_sandwich`
- Exact Lean type: `∀ (N : ℕ) (K O : Set (Euclidean N)), IsCompact K → IsOpen O → K ⊆ O → ∃ g : Euclidean N → ℝ, Continuous g ∧ HasCompactSupport g ∧ tsupport g ⊆ O ∧ ∀ ν : Measure (Euclidean N), (∀ L : Set (Euclidean N), IsCompact L → L ⊆ O → ν L ≠ ∞) → ν K ≤ ENNReal.ofReal (∫ x, g x ∂ν) ∧ ENNReal.ofReal (∫ x, g x ∂ν) ≤ ν O`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
