# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.tangential_gradient-a1.weak_limit_gluing-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-f86974e4a3/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.tangential_gradient-a1`
- Child key: `weak_limit_gluing`
- Declaration: `Submission.dor_lmbsf_tg_weak_limit_gluing`
- Exact Lean type: `∀ (P : ℕ) (μ : Measure (Euclid P)) (M E : Set (Euclid P)) (S : ℕ → Set (Euclid P)) (u : ℕ → Euclid P → ℝ) (v D : Euclid P → ℝ), MeasurableSet M → MeasurableSet E → (∀ j, MeasurableSet (S j)) → Pairwise (fun i j => Disjoint (S i) (S j)) → (∀ j, S j ⊆ M) → μ (M \ ⋃ j, S j) = 0 → IntegrableOn D M μ → (∀ k, AEStronglyMeasurable (u k) (μ.restrict M)) → (∀ k, ∀ᵐ x ∂(μ.restrict M), ‖u k x‖ ≤ D x) → IntegrableOn v (M ∩ E) μ → (∀ j, Tendsto (fun k => ∫ x in S j, u k x ∂μ) atTop (𝓝 (∫ x in S j ∩ E, v x ∂μ))) → Tendsto (fun k => ∫ x in M, u k x ∂μ) atTop (𝓝 (∫ x in M ∩ E, v x ∂μ))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
