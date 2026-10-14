# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.pushforward-a1.extension-a1.mollify-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-fad6ade501/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.pushforward-a1.extension-a1`
- Child key: `mollify`
- Declaration: `Submission.dtc_bc_lc_pf_ext_mollify_tendstoUniformly`
- Exact Lean type: `∀ (P n : ℕ) (h : Euclid P → Covector (Euclid P) n), Continuous h → HasCompactSupport h → ∃ ωs : ℕ → TestFormOn (univ : Set (Euclid P)) n, TendstoUniformly (fun j x => (ωs j : DifferentialForm (Euclid P) n) x) h atTop`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
