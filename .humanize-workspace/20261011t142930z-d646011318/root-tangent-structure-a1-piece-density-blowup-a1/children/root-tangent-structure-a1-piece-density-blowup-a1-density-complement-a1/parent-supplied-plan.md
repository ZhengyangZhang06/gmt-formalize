# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tangent_structure-a1.piece_density_blowup-a1.density_complement-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-piece-density-blowup-a1-density-complement-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tangent_structure-a1.piece_density_blowup-a1`
- Child key: `density_complement`
- Declaration: `Submission.ts_pdb_density_complement_vanish`
- Exact Lean type: `∀ (n : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) (w : EuclideanSpace ℝ (Fin n)) (R : ℝ), MeasurableSet C → 0 < R → Tendsto (fun r : ℝ ↦ volume (C ∩ closedBall w r) / volume (closedBall w r)) (𝓝[>] 0) (𝓝 1) → Tendsto (fun t : ℝ ↦ volume {u : EuclideanSpace ℝ (Fin n) | u ∈ closedBall 0 R ∧ w + t • u ∉ C}) (𝓝[>] 0) (𝓝 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
