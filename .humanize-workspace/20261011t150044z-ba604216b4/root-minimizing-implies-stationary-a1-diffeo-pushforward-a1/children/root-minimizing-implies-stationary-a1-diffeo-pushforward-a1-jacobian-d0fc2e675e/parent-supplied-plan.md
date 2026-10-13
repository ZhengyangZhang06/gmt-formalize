# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.jacobian_measurable-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-jacobian-d0fc2e675e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1`
- Child key: `jacobian_measurable`
- Declaration: `Submission.dpf_aestronglyMeasurable_gramJacobian`
- Exact Lean type: `∀ (P : ℕ) (μ : Measure (Euclid P)) (Q : Euclid P → Submodule ℝ (Euclid P)) (L : Euclid P → (Euclid P →L[ℝ] Euclid P)), AEStronglyMeasurable (fun x => (Q x).starProjection) μ → AEStronglyMeasurable L μ → AEStronglyMeasurable (fun x => Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (Module.finrank ℝ (Q x)) => inner ℝ (L x (stdOrthonormalBasis ℝ (Q x) i)) (L x (stdOrthonormalBasis ℝ (Q x) j))))) μ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
