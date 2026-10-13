# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.blowup_hypotheses-a1.rescaled_retraction-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-blowup-hypoth-81b8021bdb/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.blowup_hypotheses-a1`
- Child key: `rescaled_retraction`
- Declaration: `Submission.dtc_bc_bh_rescaled_retraction`
- Exact Lean type: `∀ (P : ℕ) (U N : Set (Euclid P)) (x : Euclid P) (δ : ℝ) (π : Euclid P → Euclid P), IsOpen U → x ∈ U → x ∈ N → 0 < δ → ContDiffOn ℝ 1 π (ball x δ) → MapsTo π (ball x δ) N → (∀ y ∈ N ∩ ball x δ, π y = y) → (∀ η : ℝ, 0 < η → ∃ s : ℝ, 0 < s ∧ s ≤ δ ∧ ∀ y ∈ ball x s, ∀ z ∈ ball x s, ‖π y - π z‖ ≤ (1 + η) * ‖y - z‖) → ∀ lams : ℕ → ℝ, (∀ j, 0 < lams j) → Tendsto lams atTop (𝓝 0) → ∀ G : ℝ, 0 < G → ∃ πs : ℕ → Euclid P → Euclid P, (∀ᶠ j in atTop, ContDiffOn ℝ 1 (πs j) (ball 0 G) ∧ MapsTo (πs j) (ball 0 G) (dilation x (lams j) '' (U ∩ N)) ∧ (∀ y ∈ dilation x (lams j) '' (U ∩ N) ∩ ball 0 G, πs j y = y) ∧ ∀ y ∈ ball 0 G, ‖πs j y‖ ≤ 2 * ‖y‖) ∧ ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ y ∈ ball 0 G, ∀ z ∈ ball 0 G, ‖πs j y - πs j z‖ ≤ (1 + η) * ‖y - z‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
