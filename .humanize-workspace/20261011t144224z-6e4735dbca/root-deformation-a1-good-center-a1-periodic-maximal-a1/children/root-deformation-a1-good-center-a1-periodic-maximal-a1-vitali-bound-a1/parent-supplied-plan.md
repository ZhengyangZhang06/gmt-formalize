# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.good_center-a1.periodic_maximal-a1.vitali_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-good-center-a1-periodic-maximal-a1-vitali-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.good_center-a1.periodic_maximal-a1`
- Child key: `vitali_bound`
- Declaration: `Submission.dgc_pm_vitali_volume_bound`
- Exact Lean type: `∀ (ι : Type) [Fintype ι] (S : Set (EuclideanSpace ℝ ι)) (r : EuclideanSpace ℝ ι → ℝ) (R M : ℝ), (∀ b ∈ S, 0 < r b ∧ r b ≤ R) → (∀ u ⊆ S, u.PairwiseDisjoint (fun b => closedBall b (r b)) → u.Countable ∧ ∑' b : u, ENNReal.ofReal (r b ^ Fintype.card ι) ≤ ENNReal.ofReal M) → volume S ≤ ENNReal.ofReal (10 ^ Fintype.card ι * M)`

## Sibling prerequisites

- `root.deformation-a1.good_center-a1.periodic_maximal-a1.ball_volume-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
