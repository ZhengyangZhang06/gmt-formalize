# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.graph_tangent-a1.graph_blowup_rescaling-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-2aec892c09/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.graph_tangent-a1`
- Child key: `graph_blowup_rescaling`
- Declaration: `Submission.doraggt_graph_blowup_rescaling`
- Exact Lean type: `∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (a : Euclid (n + k)) (f : Euclid n → Euclid k) (v : Euclid n) (r : ℝ), r ≠ 0 → Poincare.SimonGMT.Chapter03.blowUpMap (a + ι v + ι' (f v)) r '' Set.range (fun u => a + ι u + ι' (f u)) = Set.range (fun w => ι w + ι' (r⁻¹ • (f (v + r • w) - f v))) ∧ ∀ w : Euclid n, fderiv ℝ (fun w' => r⁻¹ • (f (v + r • w') - f v)) w = fderiv ℝ f (v + r • w)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
