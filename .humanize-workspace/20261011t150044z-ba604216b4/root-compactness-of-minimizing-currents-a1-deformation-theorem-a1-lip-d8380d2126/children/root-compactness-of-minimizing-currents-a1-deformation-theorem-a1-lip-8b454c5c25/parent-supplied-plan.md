# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.homotopy-a1.smooth_approx-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-8b454c5c25/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.homotopy-a1`
- Child key: `smooth_approx`
- Declaration: `Submission.cmcdt_lpoh_smooth_approx`
- Exact Lean type: `∀ (N N' : ℕ) (Λ : NNReal) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (K : Set (Euclid N)), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact K → (∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → ∃ (Fs Gs : ℕ → Euclid N → Euclid N') (Hs : ℕ → Euclid (N + 1) → Euclid N') (Λ' : ℝ), (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) ∧ (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Gs j)) ∧ (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Hs j)) ∧ (∀ (j : ℕ) (x : Euclid N), ‖fderiv ℝ (Fs j) x‖ ≤ (Λ : ℝ)) ∧ (∀ (j : ℕ) (x : Euclid N), ‖fderiv ℝ (Gs j) x‖ ≤ (Λ : ℝ)) ∧ TendstoUniformly Fs F atTop ∧ TendstoUniformly Gs G atTop ∧ (∀ (j : ℕ) (x : Euclid N), Hs j (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) = Gs j x) ∧ (∀ (j : ℕ) (x : Euclid N), Hs j (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) = Fs j x) ∧ (∀ (j : ℕ) (x v : Euclid N), fderiv ℝ (Hs j) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) = fderiv ℝ (Gs j) x v) ∧ (∀ (j : ℕ) (x v : Euclid N), fderiv ℝ (Hs j) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) = fderiv ℝ (Fs j) x v) ∧ (∀ (j : ℕ) (t : ℝ) (x : Euclid N), ‖fderiv ℝ (Hs j) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (EuclideanSpace.single 0 1)‖ ≤ dist (F x) (G x) + 2 * (Λ : ℝ) / ((j : ℝ) + 1)) ∧ (∀ (j : ℕ), ∀ t ∈ Icc (0 : ℝ) 1, ∀ (x v : Euclid N), ‖fderiv ℝ (Hs j) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v)))‖ ≤ (Λ : ℝ) * ‖v‖) ∧ (∀ (j : ℕ), ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ K, ‖fderiv ℝ (Hs j) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)))‖ ≤ Λ') ∧ TendstoUniformlyOn Hs H atTop {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ K, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))}`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.lipschitz_pushforward-a1.operators-a1.homotopy-a1.interp_calculus-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
