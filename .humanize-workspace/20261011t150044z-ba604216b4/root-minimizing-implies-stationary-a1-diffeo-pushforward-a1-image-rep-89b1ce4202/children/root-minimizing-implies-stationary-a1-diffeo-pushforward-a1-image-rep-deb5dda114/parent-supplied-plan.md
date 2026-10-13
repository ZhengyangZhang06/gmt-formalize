# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.image_representation-a1.image_imrep-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-image-rep-deb5dda114/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.image_representation-a1`
- Child key: `image_imrep`
- Declaration: `Submission.dpfir_bilipschitz_image_imrep_exists`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (φ : Euclid P → Euclid P) (Λ : NNReal) (η : Euclid P → MultiVector P n), Bijective φ → LipschitzWith Λ φ → AntilipschitzWith Λ φ → φ ⁻¹' U = U → AEStronglyMeasurable η (μHE[n].restrict R.carrier) → (∀ᵐ x ∂(μHE[n].restrict R.carrier), ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n (φ '' R.carrier) (φ x) Q ∧ IsUnitOrientationOf (η x) Q) → ∃ R' : IMRep U n, R'.carrier = φ '' R.carrier ∧ ∀ x, R'.mult (φ x) = R.mult x ∧ R'.orient (φ x) = η x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
