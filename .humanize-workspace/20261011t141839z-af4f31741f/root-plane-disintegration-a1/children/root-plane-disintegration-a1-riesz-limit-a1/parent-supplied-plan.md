# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.plane_disintegration-a1.riesz_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-plane-disintegration-a1-riesz-limit-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.plane_disintegration-a1`
- Child key: `riesz_limit`
- Declaration: `Submission.plane_disint_riesz_limit`
- Exact Lean type: `∀ (N n : ℕ) (l : Filter ℝ) (m : ℝ → Measure (Grassmannian N n)) (D : Set C(Grassmannian N n, ℝ)), l.NeBot → (∀ᶠ ρ in l, IsProbabilityMeasure (m ρ)) → Dense D → (∀ f ∈ D, ∃ c : ℝ, Tendsto (fun ρ ↦ ∫ S, f S ∂(m ρ)) l (𝓝 c)) → ∃ η : Measure (Grassmannian N n), IsProbabilityMeasure η ∧ ∀ f : C(Grassmannian N n, ℝ), Tendsto (fun ρ ↦ ∫ S, f S ∂(m ρ)) l (𝓝 (∫ S, f S ∂η))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
