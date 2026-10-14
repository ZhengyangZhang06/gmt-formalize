# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.im_cylinder-a1.orientation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-73e68503d8/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.im_cylinder-a1`
- Child key: `orientation`
- Declaration: `Submission.dimred_mbl_dt_lp_imc_orientation`
- Exact Lean type: `∀ (N n : ℕ) (ξ : MultiVector N n) (ξ' : MultiVector (N + 1) (n + 1)) (Q : Submodule ℝ (Euclid N)), IsUnitOrientationOf ξ Q → (∀ (α : Covector (Euclid (N + 1)) (n + 1)) (β : Covector (Euclid N) n), (∀ v : Fin n → Euclid N, β v = α (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) → ξ' α = ξ β) → IsUnitOrientationOf ξ' (Submodule.span ℝ (insert (EuclideanSpace.single 0 1) ((fun v : Euclid N => (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v)) : Euclid (N + 1))) '' (Q : Set (Euclid N)))))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
