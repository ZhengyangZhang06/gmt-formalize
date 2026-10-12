# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.c1_sard-a1.regular_fiber-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-c1-sard-a1-regular-fiber-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.c1_sard-a1`
- Child key: `regular_fiber`
- Declaration: `Submission.c1_sard_regular_fiber_submanifold`
- Exact Lean type: `∀ (N m k : ℕ) (M U : Set (Rn N)) (f : Rn N → Rn m), Chapter02.IsSimonSubmanifold (E := Rn (m + k)) 1 M → IsOpen U → M ⊆ U → ContDiffOn ℝ 1 f U → (∀ (V : Set (Rn (m + k))) (W : Set (Rn N)) (ψ : Rn (m + k) → Rn N), Chapter02.IsSimonLocalRepresentation 1 M V W ψ → ∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap) → ContinuousOn (coareaJacobian M f) M → ∀ y : Rn m, Chapter02.IsSimonSubmanifold (E := Rn k) 1 ((M ∩ f ⁻¹' {y}) \ {x | coareaJacobian M f x = 0})`

## Sibling prerequisites

- `root.c1_sard-a1.jacobian_rank-a1`
- `root.c1_sard-a1.level_set_chart-a1`
- `root.c1_sard-a1.chart_composition-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
