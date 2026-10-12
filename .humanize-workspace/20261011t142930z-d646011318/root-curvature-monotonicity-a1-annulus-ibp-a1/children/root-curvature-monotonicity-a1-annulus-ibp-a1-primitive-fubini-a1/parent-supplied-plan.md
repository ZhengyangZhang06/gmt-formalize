# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.curvature_monotonicity-a1.annulus_ibp-a1.primitive_fubini-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-curvature-monotonicity-a1-annulus-ibp-a1-primitive-fubini-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.curvature_monotonicity-a1.annulus_ibp-a1`
- Child key: `primitive_fubini`
- Declaration: `Submission.mcm_primitive_radial_fubini`
- Exact Lean type: `∀ (X : Type) [MeasurableSpace X] (ν : Measure X) (S : Set X) (r g : X → ℝ) (F F' : ℝ → ℝ) (σ ρ : ℝ), SFinite ν → MeasurableSet S → Measurable r → (∀ x ∈ S, r x ∈ Ioc σ ρ) → IntegrableOn g S ν → IntegrableOn F' (Ioc σ ρ) → (∀ t ∈ Icc σ ρ, F t = F σ + ∫ τ in Ioc σ t, F' τ) → IntegrableOn (fun x ↦ g x * (F (r x) - F σ)) S ν ∧ IntegrableOn (fun t ↦ F' t * ∫ x in S ∩ {x | t < r x}, g x ∂ν) (Ioc σ ρ) ∧ ∫ t in Ioc σ ρ, F' t * ∫ x in S ∩ {x | t < r x}, g x ∂ν = ∫ x in S, g x * (F (r x) - F σ) ∂ν`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
