# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.jacobian_measurable-a1.gram_det_identity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-jacobian-008b306a38/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.jacobian_measurable-a1`
- Child key: `gram_det_identity`
- Declaration: `Submission.dpf_jm_gram_det_eq_det_compression`
- Exact Lean type: `∀ (P : ℕ) (V : Submodule ℝ (Euclid P)) {ι : Type} [Fintype ι] [DecidableEq ι] (e : OrthonormalBasis ι ℝ V) (A : Euclid P →L[ℝ] Euclid P), Matrix.det (Matrix.of fun i j : ι => inner ℝ (A (e i)) (A (e j))) = (V.starProjection ∘L (A.adjoint ∘L A) ∘L V.starProjection + (ContinuousLinearMap.id ℝ (Euclid P) - V.starProjection)).det`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
