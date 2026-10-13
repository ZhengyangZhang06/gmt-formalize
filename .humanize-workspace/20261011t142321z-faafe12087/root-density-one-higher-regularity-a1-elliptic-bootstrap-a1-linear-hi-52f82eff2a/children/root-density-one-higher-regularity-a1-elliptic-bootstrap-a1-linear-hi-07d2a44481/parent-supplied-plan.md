# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1.dq_uniform_bounds-a1.form_coords-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-elliptic-bootstrap-a1-linear-hi-07d2a44481/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.elliptic_bootstrap-a1.linear_higher_regularity-a1.dq_uniform_bounds-a1`
- Child key: `form_coords`
- Declaration: `Submission.dohr_eb_lhr_dqub_form_coords`
- Exact Lean type: `∀ (L : Type) [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L], ∃ (N : ℕ) (b : Fin N → L) (C : ℝ), 0 ≤ C ∧ (∀ (f : L → ℝ) (m : ℝ), IsLinearMap ℝ f → 0 ≤ m → (∀ r, |f (b r)| ≤ m) → ∀ P, |f P| ≤ C * m * ‖P‖) ∧ ∀ (β : L → L → ℝ) (m : ℝ), (∀ P, IsLinearMap ℝ (fun Q => β Q P)) → (∀ Q, IsLinearMap ℝ (β Q)) → 0 ≤ m → (∀ r t, |β (b r) (b t)| ≤ m) → ∀ Q P, |β Q P| ≤ C * m * ‖Q‖ * ‖P‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
