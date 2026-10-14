# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.polyhedral_approximation-a1.finite_mass_approximation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-polyhedral-approximation-a1-finite-mass-approximation-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.polyhedral_approximation-a1`
- Child key: `finite_mass_approximation`
- Declaration: `Submission.polyhedral_approx_finite_mass_seq`
- Exact Lean type: `DeformationTheorem → ∀ m ℓ : ℕ, 1 ≤ ℓ → ∀ X : ℕ → GeometricCurrentOn (univ : Set (Eucl (m + 1 + ℓ))) (m + 1), (∀ k, IsIntegerMultiplicity (X k)) → (∀ k, (X k).mass + (X k).boundary.mass < ∞) → ∃ (ρ : ℕ → ℝ) (β : ℕ → LatticeFaceIndex (m + 1) (m + 1 + ℓ) → ℤ) (Pc : ℕ → GeometricCurrentOn (univ : Set (Eucl (m + 1 + ℓ))) (m + 1)), (∀ k, 0 < ρ k) ∧ Antitone ρ ∧ Tendsto ρ atTop (𝓝 0) ∧ (∀ k, IsLatticeChain (ρ k) (fun F => (β k F : ℝ)) (Pc k)) ∧ ∀ ω : TestFormOn (univ : Set (Eucl (m + 1 + ℓ))) (m + 1), Tendsto (fun k => Pc k ω - X k ω) atTop (𝓝 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
