# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.blowup_halfspace-a1.l1loc_transfer-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-cad2ba9711/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.blowup_halfspace-a1`
- Child key: `l1loc_transfer`
- Declaration: `Submission.codim1_rdo_dg_bh_l1loc_transfer`
- Exact Lean type: `∀ (m : ℕ) (Fs : ℕ → Set (Euclid (m + 1))) (F₀ : Set (Euclid (m + 1))), (∀ k, MeasurableSet (Fs k)) → MeasurableSet F₀ → (∀ R : ℝ, Tendsto (fun k => volume (symmDiff (Fs k) F₀ ∩ ball (0 : Euclid (m + 1)) R)) atTop (𝓝 0)) → (∀ f : Euclid (m + 1) → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ z in Fs k, f z) atTop (𝓝 (∫ z in F₀, f z))) ∧ (∀ s : ℝ, Tendsto (fun k => volume (Fs k ∩ ball (0 : Euclid (m + 1)) s)) atTop (𝓝 (volume (F₀ ∩ ball (0 : Euclid (m + 1)) s)))) ∧ ∀ s : ℝ, Tendsto (fun k => volume (ball (0 : Euclid (m + 1)) s \ Fs k)) atTop (𝓝 (volume (ball (0 : Euclid (m + 1)) s \ F₀)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
