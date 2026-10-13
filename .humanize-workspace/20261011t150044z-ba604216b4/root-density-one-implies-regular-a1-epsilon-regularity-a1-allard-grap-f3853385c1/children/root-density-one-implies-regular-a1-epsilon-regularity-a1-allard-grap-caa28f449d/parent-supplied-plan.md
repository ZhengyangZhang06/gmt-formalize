# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_decay-a1.planes_limit-a1.proj_limit_rank-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-caa28f449d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_decay-a1.planes_limit-a1`
- Child key: `proj_limit_rank`
- Declaration: `Submission.dorag_ted_pl_proj_limit_rank`
- Exact Lean type: `∀ (P n : ℕ) (S : ℕ → Submodule ℝ (Euclid P)) (w : Fin P → Euclid P), (∀ j, Module.finrank ℝ (S j) = n) → (∀ i : Fin P, Tendsto (fun j => (S j).starProjection (EuclideanSpace.single i (1 : ℝ))) atTop (𝓝 (w i))) → ∃ S' : Submodule ℝ (Euclid P), Module.finrank ℝ S' = n ∧ ∀ i : Fin P, S'.starProjection (EuclideanSpace.single i (1 : ℝ)) = w i`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
