# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.c1_sard-a1.critical_null-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-c1-sard-a1-critical-null-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.c1_sard-a1`
- Child key: `critical_null`
- Declaration: `Submission.c1_sard_critical_fibers_null`
- Exact Lean type: `CoareaFormula → ∀ (N m k : ℕ) (M U : Set (Rn N)) (f : Rn N → Rn m), 0 < k → Chapter02.IsSimonSubmanifold (E := Rn (m + k)) 1 M → IsOpen U → M ⊆ U → ContDiffOn ℝ 1 f U → MeasurableSet M → ContinuousOn (coareaJacobian M f) M → ∀ᵐ y ∂(volume : Measure (Rn m)), μHE[k] (M ∩ f ⁻¹' {y} ∩ {x | coareaJacobian M f x = 0}) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
