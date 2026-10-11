# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.coarea_and_slices-a1.normdet_chain_rule-a1.normdet_adjoint_horizontal-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-coarea-and-slices-a1-normdet-chain-rule-a1-normdet-adjoint-horizontal-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.coarea_and_slices-a1.normdet_chain_rule-a1`
- Child key: `normdet_adjoint_horizontal`
- Declaration: `Submission.coarea_normDet_adjoint_eq_horizontal`
- Exact Lean type: `∀ {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y] (P : X →ₗ[ℝ] Y), (Function.Surjective P → (LinearMap.adjoint P).normDet = (P ∘ₗ (LinearMap.ker P)ᗮ.subtype).normDet) ∧ (¬ Function.Surjective P → (LinearMap.adjoint P).normDet = 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
