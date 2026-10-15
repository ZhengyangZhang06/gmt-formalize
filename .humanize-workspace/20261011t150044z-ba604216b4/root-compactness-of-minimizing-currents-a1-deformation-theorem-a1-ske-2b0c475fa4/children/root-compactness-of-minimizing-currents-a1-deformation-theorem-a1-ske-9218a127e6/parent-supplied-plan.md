# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.skeleton_retraction-a1.face_radial-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-ske-9218a127e6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.skeleton_retraction-a1`
- Child key: `face_radial`
- Declaration: `Submission.cmcdtsr_face_radial`
- Exact Lean type: `∀ (P : ℕ) (a : Euclid P), (∀ i, |a i - 1 / 2| < 1 / 4) → ∀ (b : Fin P → ℤ) (J : Finset (Fin P)) (hJ : J.Nonempty) (ψF : Euclid P → Euclid P), (∀ y : Euclid P, ∀ i, ψF y i = if i ∈ J then (b i : ℝ) + a i + (y i - b i - a i) / J.sup' hJ (fun k => max ((y k - b k - a k) / (1 - a k)) ((b k + a k - y k) / a k)) else y i) → ∀ x : Euclid P, (∀ i, (i ∈ J → (b i : ℝ) ≤ x i ∧ x i ≤ b i + 1) ∧ (i ∉ J → x i = b i)) → (∃ i ∈ J, x i ≠ b i + a i) → (∀ k ∈ J, |x k - b k - a k| ≤ J.sup' hJ (fun k => max ((x k - b k - a k) / (1 - a k)) ((b k + a k - x k) / a k))) ∧ 0 < J.sup' hJ (fun k => max ((x k - b k - a k) / (1 - a k)) ((b k + a k - x k) / a k)) ∧ J.sup' hJ (fun k => max ((x k - b k - a k) / (1 - a k)) ((b k + a k - x k) / a k)) ≤ 1 ∧ (∀ i, (i ∈ J → (b i : ℝ) ≤ ψF x i ∧ ψF x i ≤ b i + 1) ∧ (i ∉ J → ψF x i = b i)) ∧ (∃ i ∈ J, ψF x i = b i ∨ ψF x i = b i + 1) ∧ ((∃ i ∈ J, x i = b i ∨ x i = b i + 1) → ψF x = x) ∧ ∀ y : Euclid P, (∀ i, (i ∈ J → (b i : ℝ) ≤ y i ∧ y i ≤ b i + 1) ∧ (i ∉ J → y i = b i)) → (∃ i ∈ J, y i ≠ b i + a i) → dist (ψF y) (ψF x) ≤ (1 + 4 * Real.sqrt J.card) / J.sup' hJ (fun k => max ((x k - b k - a k) / (1 - a k)) ((b k + a k - x k) / a k)) * dist y x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
