# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.plane_disintegration-a1.slice_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-plane-disintegration-a1-slice-density-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.plane_disintegration-a1`
- Child key: `slice_density`
- Declaration: `Submission.plane_disint_slice_density`
- Exact Lean type: `∀ (N n : ℕ) (U : Set (Euclidean N)) (V : Varifold N n U) (β : C(Grassmannian N n, ℝ)), (∀ S, 0 ≤ β S) → ∃ e : Euclidean N → ℝ, Measurable e ∧ (∀ᵐ x ∂V.weight, Tendsto (fun ρ : ℝ ↦ (∫ z in closedBall x ρ ×ˢ (univ : Set (Grassmannian N n)), β z.2 ∂V.measure) / (V.weight (closedBall x ρ)).toReal) (𝓝[>] 0) (𝓝 (e x))) ∧ ∀ A : Set (Euclidean N), MeasurableSet A → ∫⁻ z in A ×ˢ (univ : Set (Grassmannian N n)), ENNReal.ofReal (β z.2) ∂V.measure = ∫⁻ x in A, ENNReal.ofReal (e x) ∂V.weight`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
