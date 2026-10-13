# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.codim_zero-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-codim-zero-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1`
- Child key: `codim_zero`
- Declaration: `Submission.dtc_bc_codim_zero`
- Exact Lean type: `∀ (n : ℕ) (U : Set (Euclid n)) (T : GeometricCurrentOn U n) (x : Euclid n), 0 < n → IsOpen U → IsIntegerMultiplicity T → x ∈ U → x ∉ boundarySupport T → ∀ (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j), Tendsto lams atTop (𝓝 0) → ∃ C : GeometricCurrentOn (univ : Set (Euclid n)) n, ConvergesWeakly (fun j => blowUp T x (lams j) (hlams j).ne') C ∧ MassMeasuresConverge (fun j => blowUp T x (lams j) (hlams j).ne') C ∧ IsMinimizingIn C univ ∧ BoundaryVanishes C`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.blowup_compactness-a1.measure_locality-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
