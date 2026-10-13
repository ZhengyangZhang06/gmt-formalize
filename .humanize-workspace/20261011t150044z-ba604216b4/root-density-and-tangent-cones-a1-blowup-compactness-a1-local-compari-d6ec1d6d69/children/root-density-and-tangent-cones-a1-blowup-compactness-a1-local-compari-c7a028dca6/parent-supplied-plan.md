# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.pushforward-a1.extension-a1.integral_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-c7a028dca6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.pushforward-a1.extension-a1`
- Child key: `integral_limit`
- Declaration: `Submission.dtc_bc_lc_pf_ext_imrep_integral_tendsto`
- Exact Lean type: `∀ (P n : ℕ) (U K : Set (Euclid P)) (R : IMRep U n) (gs : ℕ → Euclid P → Covector (Euclid P) n) (g : Euclid P → Covector (Euclid P) n), IsCompact K → K ⊆ U → μHE[n] (R.carrier \ K) = 0 → (∀ j, Continuous (gs j)) → Continuous g → TendstoUniformlyOn gs g atTop K → Tendsto (fun j => ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (gs j x) ∂μHE[n]) atTop (𝓝 (∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (g x) ∂μHE[n]))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
