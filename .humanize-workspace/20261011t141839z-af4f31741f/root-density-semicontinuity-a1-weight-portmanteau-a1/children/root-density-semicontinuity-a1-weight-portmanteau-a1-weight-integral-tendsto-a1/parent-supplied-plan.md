# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_semicontinuity-a1.weight_portmanteau-a1.weight_integral_tendsto-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-density-semicontinuity-a1-weight-portmanteau-a1-weight-integral-tendsto-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_semicontinuity-a1.weight_portmanteau-a1`
- Child key: `weight_integral_tendsto`
- Declaration: `Submission.varifold_weight_integral_tendsto_of_radonConverges`
- Exact Lean type: `∀ (N n : ℕ) (U : Set (Euclidean N)) (Vi : ℕ → Varifold N n U) (V : Varifold N n U), Varifold.RadonConverges Vi V → ∀ g : Euclidean N → ℝ, Continuous g → HasCompactSupport g → tsupport g ⊆ U → Tendsto (fun i ↦ ∫ x, g x ∂(Vi i).weight) atTop (𝓝 (∫ x, g x ∂V.weight))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
