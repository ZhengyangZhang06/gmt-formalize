# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.finite_rays-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-8d944ececd/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1`
- Child key: `finite_rays`
- Declaration: `Submission.idtp_fons_odc_finite_rays`
- Exact Lean type: `∀ (P : ℕ) (μ : Measure (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → μ K ≠ ∞) → (∀ lam : ℝ, 0 < lam → ∀ W : Set (Euclid P), IsOpen W → μ ((fun x => lam • x) '' W) = ENNReal.ofReal lam * μ W) → (∀ x : Euclid P, (∀ ε : ℝ, 0 < ε → μ (ball x ε) ≠ 0) → ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ENNReal.ofReal ρ ≤ μ (ball x ρ)) → ∃ F : Finset (Euclid P), (∀ e ∈ F, ‖e‖ = 1) ∧ μ ((⋃ e ∈ F, (fun t : ℝ => t • e) '' Ioi 0)ᶜ) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
