# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.lipschitz_leibniz-a1.cutoff_smoothing-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-b5b5e11d13/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.lipschitz_leibniz-a1`
- Child key: `cutoff_smoothing`
- Declaration: `Submission.dor_lmbsf_ll_cutoff_smooth_approx`
- Exact Lean type: `∀ (P : ℕ) (f : Euclid P → ℝ) (L : NNReal) (a b : ℝ), LipschitzWith L f → a < b → ∃ (hs : ℕ → Euclid P → ℝ) (c : ℝ), (∀ k, ContDiff ℝ (⊤ : ℕ∞) (hs k)) ∧ (∀ k x, ‖fderiv ℝ (hs k) x‖ ≤ c) ∧ (∀ k x, |hs k x| ≤ 2) ∧ TendstoUniformly hs (fun x => min 1 (max 0 ((b - f x) / (b - a)))) atTop`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.slicing-a1.lipschitz_smoothing-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
