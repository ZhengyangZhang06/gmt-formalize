# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_height-a1.mult_one_domination-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-b1d1e3c3c6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_height-a1`
- Child key: `mult_one_domination`
- Declaration: `Submission.dorag_tes_gah_mult_one_le_hausdorff`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (B : Set (Euclid P)), MeasurableSet B → (∀ᵐ x ∂R.measure, x ∈ B → R.mult x = 1) → R.measure.restrict B ≤ (μHE[n] : Measure (Euclid P)).restrict B ∧ ∀ (A : Set (Euclid P)) (h : Euclid P → ℝ≥0∞), A ⊆ B → (∫⁻ x in A, h x ∂R.measure) ≤ ∫⁻ x in A, h x ∂μHE[n]`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
