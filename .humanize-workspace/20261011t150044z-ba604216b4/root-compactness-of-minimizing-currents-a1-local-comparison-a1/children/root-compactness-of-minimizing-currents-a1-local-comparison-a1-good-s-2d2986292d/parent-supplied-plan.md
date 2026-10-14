# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.local_comparison-a1.good_slice_level-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-local-comparison-a1-good-s-2d2986292d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.local_comparison-a1`
- Child key: `good_slice_level`
- Declaration: `Submission.lcmp_exists_good_slice_level`
- Exact Lean type: `∀ (P : ℕ) (ν κ : ℕ → Measure (Euclid P)) (f : Euclid P → ℝ) (a b : ℝ), Measurable f → a < b → (∀ j, ν j {x | a < f x ∧ f x < b} < ∞) → Tendsto (fun j => ν j {x | a < f x ∧ f x < b}) atTop (𝓝 0) → (∀ j, κ j {x | a < f x ∧ f x < b} < ∞) → ∃ t ∈ Ioo a b, ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ j, κ j {x | f x = t} = 0) ∧ (∀ j, liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν j {x | t - h < f x ∧ f x < t}) (𝓝[>] 0) < ∞) ∧ Tendsto (fun j => liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν (φ j) {x | t - h < f x ∧ f x < t}) (𝓝[>] 0)) atTop (𝓝 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
