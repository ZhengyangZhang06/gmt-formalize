# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.blowup_hypotheses-a1.domain_boundary-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-blowup-hypoth-f7a82decab/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.blowup_hypotheses-a1`
- Child key: `domain_boundary`
- Declaration: `Submission.dtc_bc_bh_blowUp_domain_boundary`
- Exact Lean type: `∀ (P m : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (m + 1)) (x : Euclid P), IsOpen U → x ∈ U → x ∉ boundarySupport T → ∀ (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j), Tendsto lams atTop (𝓝 0) → (∀ j, IsOpen (dilation x (lams j) '' U)) ∧ (∀ R : ℝ, ∀ᶠ j in atTop, closedBall (0 : Euclid P) R ⊆ dilation x (lams j) '' U) ∧ (∀ R : ℝ, ∀ᶠ j in atTop, ∀ ω : TestFormOn (dilation x (lams j) '' U) m, tsupport (ω : DifferentialForm (Euclid P) m) ⊆ ball 0 R → (blowUp T x (lams j) (hlams j).ne').boundary ω = 0)`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.vanish_off_support-a1`
- `root.density_and_tangent_cones-a1.blowup_scaling-a1.blowup_structure-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
