# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.difference_quotient_limit-a1.diffquot_uniform-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-differenc-01f01400e6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.difference_quotient_limit-a1`
- Child key: `diffquot_uniform`
- Declaration: `Submission.dohr_eb_dql_diffQuot_tendstoUniformlyOn`
- Exact Lean type: `∀ (n ℓ : ℕ) (f : Rn n → Rn ℓ) (U K : Set (Rn n)) (e : Rn n), IsOpen U → ContDiffOn ℝ 1 f U → IsCompact K → K ⊆ U → TendstoUniformlyOn (fun (d : ℝ) (x : Rn n) => d⁻¹ • (f (x + d • e) - f x)) (fun x => fderiv ℝ f x e) (𝓝[≠] 0) K`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
