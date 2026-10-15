# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.blowup_hypotheses-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-blowup-hypotheses-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1`
- Child key: `blowup_hypotheses`
- Declaration: `Submission.dimred_mbl_blowUp_hypotheses`
- Exact Lean type: `∀ (m k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (m + 1 + k))) (T : GeometricCurrentOn U (m + 1)), IsOpen U → IsEmbeddedSubmanifold 2 (m + 1 + ℓ) N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T → (∀ K : Set (Euclid (m + 1 + k)), IsCompact K → K ⊆ U → ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ (y : Euclid (m + 1 + k)) (R : ℝ), closedBall y R ⊆ K → MonotoneOn (fun ρ : ℝ => ENNReal.ofReal (Real.exp (Λ * ρ) / ρ ^ (m + 1)) * T.massOn (ball y ρ)) (Ioo 0 R)) → ∀ (x : Euclid (m + 1 + k)) (xs : ℕ → Euclid (m + 1 + k)) (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j), x ∈ U → Tendsto xs atTop (𝓝 x) → Tendsto lams atTop (𝓝 0) → (∀ j, IsOpen (dilation (xs j) (lams j) '' U)) ∧ (∀ R : ℝ, ∀ᶠ j in atTop, closedBall (0 : Euclid (m + 1 + k)) R ⊆ dilation (xs j) (lams j) '' U) ∧ (∀ j, IsMinimizingIn (blowUp T (xs j) (lams j) (hlams j).ne') (dilation (xs j) (lams j) '' (U ∩ N))) ∧ (∀ j, (blowUp T (xs j) (lams j) (hlams j).ne').support ⊆ dilation (xs j) (lams j) '' (U ∩ N)) ∧ (∀ R : ℝ, ∃ c : ℝ≥0∞, c ≠ ∞ ∧ ∀ᶠ j in atTop, (blowUp T (xs j) (lams j) (hlams j).ne').massOn (ball 0 R) ≤ c) ∧ (∀ j, (blowUp T (xs j) (lams j) (hlams j).ne').boundary = 0) ∧ ∀ G : ℝ, 0 < G → ∃ (πs : ℕ → Euclid (m + 1 + k) → Euclid (m + 1 + k)) (G' : ℝ), (∀ᶠ j in atTop, dilation (xs j) (lams j) '' (U ∩ N) ∩ ball 0 G = ∅ ∨ (ContDiffOn ℝ 1 (πs j) (ball 0 G) ∧ MapsTo (πs j) (ball 0 G) (dilation (xs j) (lams j) '' (U ∩ N) ∩ ball 0 G') ∧ ∀ y ∈ dilation (xs j) (lams j) '' (U ∩ N) ∩ ball 0 G, πs j y = y)) ∧ ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, dilation (xs j) (lams j) '' (U ∩ N) ∩ ball 0 G = ∅ ∨ ∀ y ∈ ball 0 G, ∀ z ∈ ball 0 G, ‖πs j y - πs j z‖ ≤ (1 + η) * ‖y - z‖`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.imrep_mass_and_support-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
