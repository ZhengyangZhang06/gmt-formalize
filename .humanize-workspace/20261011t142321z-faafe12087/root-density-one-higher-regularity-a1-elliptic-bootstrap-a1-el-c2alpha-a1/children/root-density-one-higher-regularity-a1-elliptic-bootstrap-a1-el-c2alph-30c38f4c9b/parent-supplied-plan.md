# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_c2alpha-a1.averaged_forcing-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-el-c2alph-30c38f4c9b/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.el_c2alpha-a1`
- Child key: `averaged_forcing`
- Declaration: `Submission.dohr_eb_elc2_averaged_forcing`
- Exact Lean type: `∀ (n ℓ : ℕ) (α H d : ℝ) (g : Rn n → Rn ℓ) (S K : Set (Rn n)) (e : Rn n), 0 < α → (∀ x ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, x + (t * d) • e ∈ K) → (∀ x ∈ K, ∀ y ∈ K, ‖g x - g y‖ ≤ H * ‖x - y‖ ^ α) → ∃ Φ : Rn n → (Rn n →L[ℝ] Rn ℓ) →L[ℝ] ℝ, (∀ (x : Rn n) (P : Rn n →L[ℝ] Rn ℓ), Φ x P = inner ℝ (∫ t in (0 : ℝ)..1, g (x + (t * d) • e)) (P e)) ∧ ∀ x ∈ S, ∀ y ∈ S, ∀ P : Rn n →L[ℝ] Rn ℓ, |Φ x P - Φ y P| ≤ H * ‖e‖ * ‖x - y‖ ^ α * ‖P‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
