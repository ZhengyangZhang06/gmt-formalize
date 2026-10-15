# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.graph_tangent-a1.graph_map_basics-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-db4db12cbd/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.graph_tangent-a1`
- Child key: `graph_map_basics`
- Declaration: `Submission.doraggt_lipschitz_graph_map_basics`
- Exact Lean type: `∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (b : Euclid (n + k)) (g : Euclid n → Euclid k) (L : NNReal), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → LipschitzWith L g → (∀ u u' : Euclid n, dist u u' ≤ dist (b + ι u + ι' (g u)) (b + ι u' + ι' (g u'))) ∧ LipschitzWith (1 + L) (fun u => b + ι u + ι' (g u)) ∧ IsClosed (Set.range fun u => b + ι u + ι' (g u)) ∧ (∀ K : Set (Euclid (n + k)), IsCompact K → μHE[n] (Set.range (fun u => b + ι u + ι' (g u)) ∩ K) ≠ ∞) ∧ ∀ N : Set (Euclid n), volume N = 0 → μHE[n] ((fun u => b + ι u + ι' (g u)) '' N) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
