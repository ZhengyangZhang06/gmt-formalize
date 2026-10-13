# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.jacobian_measurable-a1.compression_det_measurable-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-jacobian-151e42a054/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.jacobian_measurable-a1`
- Child key: `compression_det_measurable`
- Declaration: `Submission.dpf_jm_aestronglyMeasurable_sqrt_det_compression`
- Exact Lean type: `∀ (P : ℕ) (μ : Measure (Euclid P)) (p L : Euclid P → (Euclid P →L[ℝ] Euclid P)), AEStronglyMeasurable p μ → AEStronglyMeasurable L μ → AEStronglyMeasurable (fun x => Real.sqrt ((p x ∘L ((L x).adjoint ∘L L x) ∘L p x + (ContinuousLinearMap.id ℝ (Euclid P) - p x)).det)) μ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
