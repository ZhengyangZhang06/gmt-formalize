# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1`
- Child DAG node: `root.density_one_implies_regular-a1.zero_dim_minimizing_trivial-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 1 of the parent proof (a minimizing 0-current with support in N vanishes, because deleting a point of a representation lowers the mass), made precise for an arbitrary constraint set A. Uses the sibling imrep_mass_and_support (dor_imrep_massOn_eq_measure_and_support). Notation: H⁰ = μHE[0] = μH[0] (Mathlib euclideanHausdorffMeasure_zero) and H⁰({x}) = 1 (Mathlib hausdorffMeasure_zero_singleton), so H⁰(S) is the number of points of S. A 0-covector α is the scalar α(), and test 0-forms are smooth compactly supported functions.
1. Representation. T is integer multiplicity: fix R = (M, θ, ξ) ∈ IMRep U 0 with R.Represents T. Then μ_R = θH⁰⌞M.
2. Structure of M. Countable 0-rectifiability gives M ⊆ M₀ ∪ ⋃_j F_j(ℝ⁰) with H⁰(M₀) = 0; hence M₀ = ∅ (every point has H⁰-measure 1), and each F_j(ℝ⁰) is a single point since ℝ⁰ is a point; so M is countable. For compact K ⊆ U, #(M ∩ K) ≤ ∫_{M∩K} θ dH⁰ < ∞ (θ ≥ 1 on M; R.locallyIntegrable_mult). Every x ∈ M has H⁰⌞M({x}) = 1 > 0, so the almost-everywhere property R.orients holds at every x ∈ M: ⟨α, ξ(x)⟩ = s(x)·α() with s(x) ∈ {1, −1} (an orthonormal basis of a 0-dimensional space is the empty family). Consequently T(ω) = Σ_{z∈M} θ(z)s(z)ω(z) (finite sum over M ∩ spt ω) and μ_R = Σ_{z∈M} θ(z)δ_z.
3. A support point in A is a carrier point. Suppose, for contradiction, that x ∈ spt T ∩ A. By imrep_mass_and_support (ii), x ∈ U and x ∈ spt μ_R. Choose r > 0 with B̄_r(x) ⊆ U. M ∩ B̄_r(x) is finite; if x ∉ M, then some ball B_{r'}(x), 0 < r' ≤ r, misses M, so μ_R(B_{r'}(x)) = 0, contradicting x ∈ spt μ_R. Hence x ∈ M; put m := θ(x) ≥ 1 and s := s(x).
4. The point current. Define D(ω) := m·s·ω(x) for ω ∈ 𝒟⁰(U). D is linear, and D(ω_j) → 0 whenever ω_j → 0 in 𝒟⁰(U) (then ω_j → 0 uniformly on a compact set containing all supports, so ω_j(x) → 0). So D ∈ 𝒟₀(U); put S := T − D ∈ 𝒟₀(U) (the contract's difference of currents).
5. S is integer multiplicity. Let R' have carrier M' := M ∖ {x} and the same θ, ξ. M' is Borel, M' ⊆ U, M' is countable hence countably 0-rectifiable, θ ≥ 1 on M', ∫_{M'∩K}θ dH⁰ ≤ ∫_{M∩K}θ dH⁰ < ∞, and ξ is a.e. strongly measurable for H⁰⌞M'. Orientation condition at y ∈ M': for f ∈ C_c(ℝ^P), ∫_{η_{y,λ}(M')} f dH⁰ = ∫_{η_{y,λ}(M)} f dH⁰ − f((x − y)/λ) (η_{y,λ}(w) = (w − y)/λ is injective and only finitely many terms are non-zero), and f((x − y)/λ) = 0 once λ < |x − y|/a, where spt f ⊆ B_a(0). Hence the blow-ups of M' and of M at y have the same limit, so M' has the approximate tangent space {0} at y, oriented by ξ(y). Thus R' ∈ IMRep U 0, and for ω ∈ 𝒟⁰(U): R'.action(ω) = ∫_M θ⟨ω, ξ⟩ dH⁰ − θ(x)⟨ω(x), ξ(x)⟩ = T(ω) − D(ω) = S(ω). So S is integer multiplicity, represented by R'.
6. spt(S − T) = {x}. S − T = −D. If W is open and x ∈ W, pick φ ∈ C^∞_c(W) with φ(x) = 1; then D(φ) = m·s ≠ 0, so −D does not vanish on W. If x ∉ W, D vanishes on W. Hence the zero region of S − T is the union of the open W with compact closure in U and x ∉ W, which equals U ∖ {x} (every z ∈ U ∖ {x} has a ball with compact closure in U that misses x). Therefore spt(S − T) = U ∖ (U ∖ {x}) = {x}, a compact set.
7. Contradiction with minimality. Let W := B_r(x): W is open and W̄ = B̄_r(x) is a compact subset of U. spt(S − T) = {x} ⊆ A ∩ W since x ∈ A, S is integer multiplicity, and the boundary condition is vacuous in degree 0. Minimality gives M_W(T) ≤ M_W(S). By imrep_mass_and_support (i), applied to (T, R) and to (S, R'): M_W(T) = μ_R(W) = Σ_{z∈M∩W} θ(z), a finite sum (step 2), and M_W(S) = μ_{R'}(W) = μ_R(W) − m ≤ μ_R(W) − 1 < M_W(T). This contradiction shows spt T ∩ A = ∅.

## Key steps

1. A 0-dimensional representation has a countable, locally finite carrier, with orientation ±1 at every carrier point.
2. By the support identity, a point of spt T ∩ A is a carrier point x.
3. Deleting x gives an integer multiplicity competitor S with spt(S − T) = {x} ⊆ A ∩ B_r(x).
4. By the mass formula, M_W(S) = M_W(T) − θ(x) < M_W(T), contradicting minimality.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `rg -c sorry local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `rg -n -i 'allard|constancy theorem|slice|flat metric|nearest.point|nearestPoint|tubular' lake-packages-25730c7c/simongmt/Poincare/SimonGMT -t lean -l`
- `rg -n 'massOn.*=.*measure|massOn_eq|mass_eq_' lake-packages-25730c7c/simongmt/Poincare/SimonGMT -t lean`
- `rg -n 'measure_compl_support|mem_support_iff' local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `rg -n 'hausdorffMeasure_zero_singleton|euclideanHausdorffMeasure_zero' local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -n '^(theorem|lemma|def|structure|class|abbrev) ' simongmt Chapter04/{Basic,Density,MeanCurvature,FirstVariation}.lean Chapter05/Basic.lean Chapter06/{Mass,Currents,CurrentLocalEquality,AffineCurrentPushforward}.lean`
- `rg -n -i 'pushforward|slice|slicing|constancy' simongmt Chapter06/*.lean`
- `rg -l 'dor_imrep|dor_zero_dim|dor_stationary|dor_minimizing' simongmt GMT dag.json (name-collision check: no match)`
- `lake env lean /tmp/ch07-dor-decomp/Check.lean (contract text + five child types)`
- `lean -o /tmp/ch07-dor-decomp/build/DorContract.olean (byte copy of Contract.lean); lean /tmp/ch07-dor-decomp/Final.lean (#check of the exact frozen strings)`
- `lean /tmp/ch07-dor-decomp/Assembly2.lean (#print axioms dor_assembly)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Representation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/FirstVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/MeanCurvature.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter05/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/ConstancyCorrected.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/tmp/ch07-dor-decomp/Check.lean`
- `/tmp/ch07-dor-decomp/Final.lean`
- `/tmp/ch07-dor-decomp/Assembly2.lean`
- `/tmp/ch07-dor-decomp/spec/statements.json`

Snapshot: project b4d606d, mathlib 25730c7c. The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean, and its only sorry is the final main_theorem.

Reusable facts found:
- Mathlib Measure.measure_compl_support and mem_support_iff_forall (Support.lean). Used for the support identity and for showing that μ_R is carried by spt T.
- Mathlib hausdorffMeasure_zero_singleton and euclideanHausdorffMeasure_zero. H⁰ is the counting measure, which the n = 0 child uses.
- SimonGMT Chapter04/MeanCurvature.lean HasGeneralizedMeanCurvatureIn.exp_normalizedBallMass_monotoneOn: closed-ball monotonicity of e^{Λρ}ρ^{−n}μ(B̄_ρ) for the library RectifiableVarifold, usable for mean_curvature_monotonicity once IMRep is bridged.

Not available, so cited from Simon as in the parent proof:
- Allard regularity: Chapter05/Basic.lean states that Lipschitz approximation, excess decay and Allard are not formalized.
- The current Constancy Theorem 6.2.34: the Chapter08 Constancy* files concern the stationary-varifold constancy theorem.
- Slicing of integer multiplicity currents and flat convergence (6.4.5, 6.7.2): no matches.
- C¹ or Lipschitz push-forward of currents: only GeometricCurrentOn.affinePushforward for proper affine maps.
- The mass formula M_W(T) = μ_T(W) for the contract's Euclidean coefficient norm: Chapter06/Representation.lean only has the assumed field MassRepresentation.mass_characterization, for the comass Current API.

Lean checks:
- All five child types elaborate with the frozen definitions.
- The conditional assembly of DensityOneImpliesRegular from three of them plus MinimizingImpliesStationary depends only on propext, Classical.choice, Quot.sound and the stub sorryAx.
- The DAG reserves only the root's ten children, and the five dor_-prefixed names have no matches.
