# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.onto_skeleton-a1.telescope_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-telescope-limit-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.onto_skeleton-a1`
- Child key: `telescope_limit`
- Declaration: `Submission.deformation_telescope_limit`
- Exact Lean type: `∀ (N k : ℕ) (A B : ℕ → GeometricCurrentOn (univ : Set (Eucl N)) k), (∀ ν ω, A (ν + 1) ω = A ν ω + B ν ω) → (∑' ν, (B ν).mass) < ∞ → ∃ A' : GeometricCurrentOn (univ : Set (Eucl N)) k, WeaklyConvergesOn A A' ∧ A'.mass ≤ (A 0).mass + ∑' ν, (B ν).mass ∧ (∀ (ν : ℕ) (Dν : GeometricCurrentOn (univ : Set (Eucl N)) k), (∀ ω, Dν ω = A' ω - A ν ω) → Dν.mass ≤ ∑' μ, (B (μ + ν)).mass) ∧ ∀ F : Set (Eucl N), IsClosed F → (∀ ν, (A ν).support ⊆ F) → A'.support ⊆ F`

## Sibling prerequisites

- `root.compactness_mass_bounds-a1.mass_bound-a1`
- `root.integrality_weak_limits-a1.cycle_reduction-a1.support_lemmas-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
