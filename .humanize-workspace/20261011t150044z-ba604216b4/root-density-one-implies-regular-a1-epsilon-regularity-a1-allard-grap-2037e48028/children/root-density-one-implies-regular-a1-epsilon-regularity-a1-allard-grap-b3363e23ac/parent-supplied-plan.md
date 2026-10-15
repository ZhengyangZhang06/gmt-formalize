# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_variation-a1.vertical_field_variation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-b3363e23ac/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_variation-a1`
- Child key: `vertical_field_variation`
- Declaration: `Submission.dorag_tes_gv_vertical_field_first_variation`
- Exact Lean type: `∀ (m n : ℕ) (U : Set (Euclid m)) (R : IMRep U n) (ζ : Euclid m → ℝ) (e : Euclid m), Differentiable ℝ ζ → R.firstVariation (fun x => ζ x • e) = ∫ x, fderiv ℝ ζ x ((approxTangentPlane n R.carrier x).starProjection e) ∂R.measure`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
