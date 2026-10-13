# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.tangent_measure-a1.c1_to_cc_extension-a1.smooth_approx-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-tangent-measure-a1-c1-to-cc-extension-a1-smooth-approx-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.tangent_measure-a1.c1_to_cc_extension-a1`
- Child key: `smooth_approx`
- Declaration: `Submission.deGiorgiTM_cc_contDiff_approx`
- Exact Lean type: `∀ (N : ℕ) (f : Rn N → ℝ) (R δ : ℝ), Continuous f → HasCompactSupport f → (∀ z, f z ≠ 0 → ‖z‖ < R - 1) → 0 < δ → ∃ φ : Rn N → ℝ, ContDiff ℝ 1 φ ∧ HasCompactSupport φ ∧ (∀ z, |φ z - f z| ≤ δ) ∧ ∀ z, φ z ≠ 0 → ‖z‖ < R`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
