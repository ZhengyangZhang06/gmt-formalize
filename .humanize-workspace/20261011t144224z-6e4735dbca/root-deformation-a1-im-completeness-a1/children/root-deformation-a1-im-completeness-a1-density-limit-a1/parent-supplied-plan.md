# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.im_completeness-a1.density_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-im-completeness-a1-density-limit-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.im_completeness-a1`
- Child key: `density_limit`
- Declaration: `Submission.imc_im_density_limit`
- Exact Lean type: `∀ (N k : ℕ) (M : ℕ → Set (Eucl N)) (θ : ℕ → Eucl N → ℝ) (ξ : ℕ → Eucl N → NVector (Eucl N) k), (∀ p, IsRectifiableTriple (univ : Set (Eucl N)) k (M p) (θ p) (ξ p)) → (∀ p, ∀ x ∈ M p, ∃ m : ℕ, θ p x = m) → (∑' p, ∫⁻ x, ENNReal.ofReal (Real.sqrt (∑ γ : SimonMultiIndex k N, (euclideanNVectorCoordinate ((M (p + 1)).indicator (fun y => θ (p + 1) y • ξ (p + 1) y) x - (M p).indicator (fun y => θ p y • ξ p y) x) γ) ^ 2)) ∂(μHE[k] : Measure (Eucl N))) ≠ ∞ → ∃ (M₀ : Set (Eucl N)) (θ₀ : Eucl N → ℝ) (ξ₀ : Eucl N → NVector (Eucl N) k), IsRectifiableTriple (univ : Set (Eucl N)) k M₀ θ₀ ξ₀ ∧ (∀ x ∈ M₀, ∃ m : ℕ, θ₀ x = m) ∧ ∀ ω : Eucl N → Covector (Eucl N) k, Continuous ω → HasCompactSupport ω → Tendsto (fun p => tauAction k (M p) (θ p) (ξ p) ω) atTop (𝓝 (tauAction k M₀ θ₀ ξ₀ ω))`

## Sibling prerequisites

- `root.deformation-a1.im_completeness-a1.l1_cauchy_limit-a1`
- `root.deformation-a1.im_completeness-a1.limit_triple-a1`
- `root.polyhedral_approximation-a1.pairing_expansion-a1`
- `root.boundary_rectifiability-a1.local_to_global_im-a1.tau_integrable-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
