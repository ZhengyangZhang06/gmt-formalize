# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.retraction-a1.normal_coordinates-a1.linear_iso-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-retraction-a-c42bc76ee3/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.retraction-a1.normal_coordinates-a1`
- Child key: `linear_iso`
- Declaration: `Submission.dor_lmb_ret_nc_linear_iso`
- Exact Lean type: `∀ (P d : ℕ) (L : Euclid d →L[ℝ] Euclid P), Injective L → ∃ Λ : (Euclid d × ↥(L.range)ᗮ) ≃L[ℝ] Euclid P, ∀ (w : Euclid d) (k : ↥(L.range)ᗮ), Λ (w, k) = L w + k`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
