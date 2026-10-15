# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.threshold_reduction-a1.blowup_class-a1.class_tangent-a1.zero_scale_iterate-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1-blowup-cla-ef064c0dab/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.threshold_reduction-a1.blowup_class-a1.class_tangent-a1`
- Child key: `zero_scale_iterate`
- Declaration: `Submission.dimred_tr_bc_ct_zero_scale_iterate`
- Exact Lean type: `(∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (xs : ℕ → Euclid P) (lams : ℕ → ℝ) (hlams : ∀ i, 0 < lams i) (S : GeometricCurrentOn (univ : Set (Euclid P)) n) (y : Euclid P) (ss : ℕ → ℝ) (hss : ∀ k, 0 < ss k) (C : GeometricCurrentOn (univ : Set (Euclid P)) n), IsOpen U → x ∈ U → Tendsto xs atTop (𝓝 x) → Tendsto lams atTop (𝓝 0) → Tendsto ss atTop (𝓝 0) → (∃ δ Γ : ℝ, 0 < δ ∧ ∀ x' ∈ ball x δ, ∀ ρ : ℝ, 0 < ρ → ρ < δ → T.massOn (ball x' ρ) ≤ ENNReal.ofReal (Γ * ρ ^ n)) → ConvergesWeakly (fun i => blowUp T (xs i) (lams i) (hlams i).ne') S → ConvergesWeakly (fun k => blowUp S y (ss k) (hss k).ne') C → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvergesWeakly (fun k => blowUp T (xs (φ k) + lams (φ k) • y) (lams (φ k) * ss k) (mul_pos (hlams (φ k)) (hss k)).ne') C) → ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (z : Euclid P) (r : ℝ) (S : GeometricCurrentOn (univ : Set (Euclid P)) n) (cs : ℕ → Euclid P) (ts : ℕ → ℝ) (hts : ∀ i, 0 < ts i) (b y : Euclid P) (ss : ℕ → ℝ) (hss : ∀ k, 0 < ss k) (C : GeometricCurrentOn (univ : Set (Euclid P)) n), IsOpen U → b ∈ U → (∀ i, dist (cs i) z < r - ts i) → Tendsto ts atTop (𝓝 0) → Tendsto cs atTop (𝓝 b) → ConvergesWeakly (fun i => blowUp T (cs i) (ts i) (hts i).ne') S → (∃ δ Γ : ℝ, 0 < δ ∧ ∀ x' ∈ ball b δ, ∀ ρ : ℝ, 0 < ρ → ρ < δ → T.massOn (ball x' ρ) ≤ ENNReal.ofReal (Γ * ρ ^ n)) → ‖y‖ < 1 → Tendsto ss atTop (𝓝 0) → ConvergesWeakly (fun k => blowUp S y (ss k) (hss k).ne') C → ∃ (cs' : ℕ → Euclid P) (ts' : ℕ → ℝ) (hts' : ∀ i, 0 < ts' i), (∀ i, dist (cs' i) z < r - ts' i) ∧ Tendsto ts' atTop (𝓝 0) ∧ Tendsto cs' atTop (𝓝 b) ∧ ConvergesWeakly (fun i => blowUp T (cs' i) (ts' i) (hts' i).ne') C`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
