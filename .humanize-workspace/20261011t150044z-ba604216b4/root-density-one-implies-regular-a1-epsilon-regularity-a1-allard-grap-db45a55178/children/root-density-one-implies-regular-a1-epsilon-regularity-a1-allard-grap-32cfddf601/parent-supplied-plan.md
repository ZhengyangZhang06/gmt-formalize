# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.graph_c1-a1.graph_pushforward-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-32cfddf601/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.graph_c1-a1`
- Child key: `graph_pushforward`
- Declaration: `Submission.dorag_gc_graph_map_volume_le_measure`
- Exact Lean type: `∀ (n k P : ℕ) (U W : Set (Euclid P)) (R : IMRep U n) (ι : Euclid n →ₗᵢ[ℝ] Euclid P) (ι' : Euclid k →ₗᵢ[ℝ] Euclid P) (f : Euclid n → Euclid k) (z : Euclid P) (A : Set (Euclid n)), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → Continuous f → μHE[n] ((R.measure.support ∩ W) \ R.carrier) = 0 → (∀ v ∈ A, z + ι v + ι' (f v) ∈ R.measure.support ∩ W) → Measure.map (fun v => z + ι v + ι' (f v)) (volume.restrict A) ≤ R.measure.restrict ((fun v => z + ι v + ι' (f v)) '' A)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
