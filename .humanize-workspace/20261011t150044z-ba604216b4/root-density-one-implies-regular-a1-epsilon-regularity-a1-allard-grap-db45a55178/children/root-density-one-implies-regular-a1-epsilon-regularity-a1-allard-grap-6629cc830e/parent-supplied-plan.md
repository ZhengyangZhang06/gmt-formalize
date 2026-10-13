# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.graph_c1-a1.c1_criterion-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-6629cc830e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.graph_c1-a1`
- Child key: `c1_criterion`
- Declaration: `Submission.dorag_gc_contDiffOn_of_ae_hasFDerivAt`
- Exact Lean type: `∀ (n k : ℕ) (f : Euclid n → Euclid k) (L : NNReal) (Ω : Set (Euclid n)) (g : Euclid n → (Euclid n →L[ℝ] Euclid k)), 0 < n → LipschitzWith L f → IsOpen Ω → ContinuousOn g Ω → (∀ᵐ v ∂volume, v ∈ Ω → HasFDerivAt f (g v) v) → ContDiffOn ℝ 1 f Ω`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
