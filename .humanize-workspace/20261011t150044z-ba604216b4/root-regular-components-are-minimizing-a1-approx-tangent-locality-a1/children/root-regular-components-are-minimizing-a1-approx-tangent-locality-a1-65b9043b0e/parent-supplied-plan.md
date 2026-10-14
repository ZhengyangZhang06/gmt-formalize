# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_components_are_minimizing-a1.approx_tangent_locality-a1.local_density_zero-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-approx-tangent-locality-a1-65b9043b0e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_components_are_minimizing-a1.approx_tangent_locality-a1`
- Child key: `local_density_zero`
- Declaration: `Submission.regcomp_atl_local_density_zero`
- Exact Lean type: `∀ (P n : ℕ) (U S : Set (Euclid P)), IsOpen U → MeasurableSet S → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (S ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∈ U → x ∉ S → Tendsto (fun ρ : ℝ => μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0)`

## Sibling prerequisites

- `root.regular_components_are_minimizing-a1.approx_tangent_locality-a1.upper_density_zero-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
