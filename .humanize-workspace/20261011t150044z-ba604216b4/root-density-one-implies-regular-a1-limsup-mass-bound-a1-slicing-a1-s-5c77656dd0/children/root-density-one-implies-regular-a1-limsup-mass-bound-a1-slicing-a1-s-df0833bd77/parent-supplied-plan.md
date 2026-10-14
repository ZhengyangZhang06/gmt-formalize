# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.chart_pieces-a1.chart_c1_pieces-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-df0833bd77/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.chart_pieces-a1`
- Child key: `chart_c1_pieces`
- Declaration: `Submission.dor_lmbsf_cp_chart_c1_pieces`
- Exact Lean type: `(∀ (m : ℕ) (u : Euclid m → ℝ) (K : NNReal), LipschitzWith K u → ∀ ε : ℝ≥0∞, 0 < ε → ∃ G : Euclid m → ℝ, ContDiff ℝ 1 G ∧ volume {y | u y ≠ G y} < ε) → ∀ (m P : ℕ) (V : Set (Euclid m)) (ψ : Euclid m → Euclid P) (f : Euclid P → ℝ) (L : NNReal), IsOpen V → ContDiffOn ℝ 1 ψ V → LipschitzWith L f → ∃ (C C' : ℕ → Set (Euclid m)) (F : ℕ → Euclid m → ℝ), (∀ k, IsCompact (C k) ∧ IsCompact (C' k) ∧ Convex ℝ (C' k) ∧ C k ⊆ interior (C' k) ∧ C' k ⊆ V ∧ ContDiff ℝ 1 (F k) ∧ ∀ y ∈ C k, f (ψ y) = F k y) ∧ volume (V \ ⋃ k, C k) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
