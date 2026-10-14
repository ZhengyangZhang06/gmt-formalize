# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.im_cylinder-a1.cylinder_imrep-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-976c0c8303/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.im_cylinder-a1`
- Child key: `cylinder_imrep`
- Declaration: `Submission.dimred_mbl_dt_lp_imc_cylinder_imrep`
- Exact Lean type: `∀ (N n : ℕ) (R : IMRep (univ : Set (Euclid N)) n), ∫⁻ x in R.carrier, (R.mult x : ℝ≥0∞) ∂μHE[n] ≠ ∞ → ∃ R' : IMRep (univ : Set (Euclid (N + 1))) (n + 1), R'.carrier = (fun p : ℝ × Euclid N => (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (N + 1))) '' (Ioo (0 : ℝ) 1 ×ˢ R.carrier) ∧ (∀ (t : ℝ) (x : Euclid N), R'.mult (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = R.mult x) ∧ ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ (t : ℝ) (α : Covector (Euclid (N + 1)) (n + 1)) (β : Covector (Euclid N) n), (∀ v : Fin n → Euclid N, β v = α (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) → R'.orient (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) α = R.orient x β`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.im_cylinder-a1.product_null-a1`
- `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.im_cylinder-a1.cylinder_measure-a1`
- `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.im_cylinder-a1.cylinder_tangent-a1`
- `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.im_cylinder-a1.orientation-a1`
- `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.im_cylinder-a1.cylinder_rectifiable-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
