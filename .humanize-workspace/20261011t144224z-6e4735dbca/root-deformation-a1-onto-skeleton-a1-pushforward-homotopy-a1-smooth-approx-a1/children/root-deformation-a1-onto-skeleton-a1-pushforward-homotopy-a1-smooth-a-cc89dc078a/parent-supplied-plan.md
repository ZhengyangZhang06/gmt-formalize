# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_approx-a1.mollify-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-a-cc89dc078a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_approx-a1`
- Child key: `mollify`
- Declaration: `Submission.dph_sa_mollify_lipschitz`
- Exact Lean type: `∀ (m m' : ℕ) (F : Eucl m → Eucl m') (L : ℝ≥0), LipschitzWith L F → ∀ σ : ℝ, 0 < σ → ∃ Fs : Eucl m → Eucl m', ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Fs ∧ LipschitzWith L Fs ∧ (∀ x, ‖Fs x - F x‖ ≤ (L : ℝ) * σ) ∧ (∀ (x : Eucl m) (Λ' : ℝ≥0), LipschitzOnWith Λ' F (ball x (2 * σ)) → LipschitzOnWith Λ' Fs (ball x σ) ∧ ‖fderiv ℝ Fs x‖ ≤ (Λ' : ℝ) ∧ ‖Fs x - F x‖ ≤ (Λ' : ℝ) * σ) ∧ ∀ (x : Eucl m) (i : Fin m') (c : ℝ), (∀ y ∈ ball x σ, F y i = c) → Fs x i = c`

## Sibling prerequisites

- `root.slicing-a1.slice_mass_bound-a1.smooth_approx-a1.mollifier-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
