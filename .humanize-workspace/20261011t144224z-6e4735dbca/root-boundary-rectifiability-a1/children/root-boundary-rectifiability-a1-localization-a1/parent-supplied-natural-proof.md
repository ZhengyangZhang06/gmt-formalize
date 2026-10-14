# Parent-supplied natural-language proof

- Parent DAG node: `root.boundary_rectifiability-a1`
- Child DAG node: `root.boundary_rectifiability-a1.localization-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2, 3 and 6 of the parent proof (localization by slicing, printed 4.5 as used in the proof of 6.2, and the local agreement), with (P1)–(P3) specialized to what is needed: only restrictions of T and ∂T to open balls occur, and their uniqueness and mass bounds are proved directly with cut-off functions (no Riesz representation is needed); the localized current is written directly as τ(M ∩ B_r(x₀), θ, ξ) on ℝ^P (the parent's T⌞B_r(x₀) extended by zero, P3). `SlicingTheorem` is a hypothesis of this statement; it is discharged by the sibling node root.slicing-a1 in the parent's assembly.

Notation. n := m + 1, H := Hⁿ = `μHE[n]`. T = τ(M,θ,ξ) with `IsRectifiableTriple U n M θ ξ` and θ(x) ∈ ℕ on M. |α| = `covectorEuclideanNorm α`, ‖ω‖ := sup_x|ω(x)|, ‖α‖_op the operator norm. B_s := B_s(x₀).

Preliminaries.
(H0) Both |·| and ‖·‖_op are norms on the finite-dimensional space of n-covectors (|α| is the Euclidean norm of the coefficient vector (α(e_I))_I, and an alternating map vanishing on all increasing basis tuples is 0), so ‖α‖_op ≤ c|α| for a constant c = c(n,P). For orthonormal τ, |simpleNVector(τ)(α)| = |α(τ)| ≤ ‖α‖_op ≤ c|α|. Hence |⟨α, ξ(x)⟩| ≤ c|α| for H-a.e. x ∈ M (orientation property).
(H1) (Mass estimate.) If Z ∈ D_k(V), W is open, ω ∈ D^k(V) with tsupport ω ⊆ W and M_W(Z) < ∞, then |Z(ω)| ≤ M_W(Z)‖ω‖ (for s > ‖ω‖, ±ω/s are admissible for M_W(Z); let s ↓ ‖ω‖).
(H2) (τ-restrictions.) Let A ⊆ ℝ^P be Borel with A ⊆ K₀ for a compact K₀ ⊆ U, and T_A(ω) := ∫_{M∩A}θ⟨ω,ξ⟩dH for smooth compactly supported n-forms ω on ℝ^P. Then |T_A(ω)| ≤ c‖ω‖∫_{M∩K₀}θ dH < ∞ by (H0), T_A is linear, and it is sequentially continuous (test-form convergence implies uniform convergence). So T_A defines currents in Dₙ(U) and in Dₙ(ℝ^P), and for every open W, M_W(T_A) ≤ c∫_{M∩K₀}θ dH. In particular (A = closure W) T has locally finite mass: M_W(T) < ∞ for W ⊂⊂ U.
(H3) (Cut-offs.) For a ∈ ℝ^P and 0 < s < t there is a smooth χ with 0 ≤ χ ≤ 1, χ = 1 on B_s(a) and tsupport χ ⊆ B_t(a) (e.g. a `ContDiffBump` with radii s < t′ < t).
(H4) (Restrictions to an open ball.) Let B_t with B̄_t ⊆ U, Z ∈ D_k(U), and S ∈ D_k(U) with `IsRestriction Z {x ∈ U : |x − x₀| < t} S`, i.e. (the set equals B_t) there are a measure μ and v : ℝ^P → k-vectors with `IsMeasureRepresentation Z μ v` (v(ω) := ⟨ω,v⟩ is μ-integrable and Z(ω) = ∫v(ω)dμ for all ω ∈ D^k(U)) and S(ω) = ∫_{B_t}v(ω)dμ. By (H3) choose smooth χ_j, 0 ≤ χ_j ≤ 1, tsupport χ_j ⊆ B_t, χ_j = 1 on B_{t(1−2/j)} (j ≥ 3); then χ_j → 1_{B_t} pointwise. For ω ∈ D^k(U): χ_jω ∈ D^k(U), tsupport χ_jω ⊆ B_t ∩ tsupport ω, ⟨χ_jω, v⟩ = χ_j⟨ω,v⟩, and by dominated convergence (dominant |⟨ω,v⟩| ∈ L¹(μ)), (i) S(ω) = lim_j Z(χ_jω). Consequently: (ii) S is uniquely determined by Z and t; (iii) if |ω(x)| ≤ 1 for all x then χ_jω is mass-admissible for B_t, so Z(χ_jω) ≤ M_{B_t}(Z) and S(ω) ≤ M_{B_t}(Z) (when finite). Similarly, by dominated convergence in the τ-integral, (iv) T_{B_t}(ω) = lim_jT(χ_jω) for ω ∈ Dⁿ(U); with (i) and (ii), any S with `IsRestriction T B_t S` equals T_{B_t} on Dⁿ(U).

Proof.
1. (Radii.) Fix x₀ ∈ U and choose r₀ > 0 with B̄_{3r₀} ⊆ U. Put W := B_{2r₀} (open, closure B̄_{2r₀} compact ⊆ U, so W ⊂⊂ U), K₀ := B̄_{r₀}, and f(x) := |x − x₀|, which is 1-Lipschitz on ℝ^P (in particular `LipschitzOnWith 1 f U`).
2. (Slicing.) The hypotheses of `SlicingTheorem` hold for T: M_{W′}(T) < ∞ (H2) and M_{W′}(∂T) < ∞ (hypothesis) for every W′ ⊂⊂ U. It yields S_t ∈ D_m(U) (t ∈ ℝ) with `IsSlice T f t S_t` for all t, and the mass estimate (4.10).
3. (A good radius.) Apply the mass estimate with the open set W ⊆ U, L_W := 1, a := r₀/2, b := r₀ and R := T_{A′}, A′ := {x ∈ U : r₀/2 < f(x) < r₀} (Borel, A′ ⊆ K₀ ⊆ U). Its hypotheses: ‖Df(x)‖ ≤ 1 at every x (where f is differentiable this follows from the Lipschitz bound, Mathlib `norm_fderiv_le_of_lipschitz`; elsewhere `fderiv` is 0), and `IsRestriction T A′ T_{A′}` holds with the representation μ := H⌞M, v := θξ: for ω ∈ Dⁿ(U), v(ω) = θ⟨ω,ξ⟩ is μ-integrable (bounded by c‖ω‖θ on M ∩ tsupport ω by (H0), zero off tsupport ω) and T(ω) = ∫v(ω)dμ, while T_{A′}(ω) = ∫_{A′}v(ω)dμ (`Measure.restrict_restrict`). We obtain a measurable g ≥ 0 with M_W(S_t) ≤ g(t) for t ∈ (r₀/2, r₀) and ∫_{r₀/2}^{r₀}g ≤ M_W(T_{A′}) ≤ c∫_{M∩K₀}θ dH < ∞ (H2). Hence g < ∞ a.e. on (r₀/2, r₀); fix r ∈ (r₀/2, r₀) with g(r) < ∞, so M_W(S_r) < ∞. Note 0 < r and B_r ⊆ B_{3r₀} ⊆ U.
4. (Identifying the slice terms.) A := {x ∈ U : f(x) < r} = B_r. By `IsSlice T f r S_r` there are A₁ ∈ Dₙ(U), B₁ ∈ D_m(U) with `IsRestriction T A A₁`, `IsRestriction T.boundary A B₁` and S_r(ψ) = A₁(dψ) − B₁(ψ) for ψ ∈ D^m(U). By (H4)(iv), A₁(η) = T_{B_r}(η) = ∫_{M∩B_r}θ⟨η,ξ⟩dH for η ∈ Dⁿ(U). By (H4)(iii) applied to Z = ∂T, B₁(ψ) ≤ M_{B_r}(∂T) ≤ M_W(∂T) < ∞ whenever |ψ(x)| ≤ 1 for all x (B_r ⊆ W ⊂⊂ U).
5. (The current X.) Define X(η) := ∫_{M∩B_r}θ⟨η,ξ⟩dH for η ∈ Dⁿ(ℝ^P). By (H2) (A = B_r ⊆ K₀), X ∈ Dₙ(ℝ^P) and M(X) ≤ c∫_{M∩K₀}θ dH < ∞. If η ∈ Dⁿ(U) with tsupport η ⊆ B_r, then, regarding η as a test form on ℝ^P (`testFormOnInclusion`, same underlying form), X(η) = ∫_{M∩B_r}θ⟨η,ξ⟩dH = ∫_Mθ⟨η,ξ⟩dH = T(η), since the integrand vanishes on M ∖ B_r ⊆ M ∖ tsupport η.
6. (X is integer multiplicity.) X = τ(M_r,θ,ξ) with M_r := M ∩ B_r. The triple conditions on ℝ^P: M_r ⊆ ℝ^P; M_r is null-measurable (M is, B_r is open); M_r ⊆ M is countably n-rectifiable; θ > 0, θ ∈ ℕ on M_r; for compact K, M_r ∩ K ⊆ M ∩ K₀ on which θ is integrable; ξ is a.e. strongly measurable for H⌞M_r ≤ H⌞M. Orientation: for H⌞M_r-a.e. x we have x ∈ M_r and, by the orientation property of T, an orthonormal τ with `HasWeightedApproximateTangentSpaceAt n M θ x (span τ)` and ξ(x) = ±simpleNVector τ; by the sibling tangent_locality with (M,θ), (M′,θ′) := (M ∩ B_r, θ), V := B_r (open, x ∈ B_r; (M Δ (M∩B_r)) ∩ B_r = ∅), `HasWeightedApproximateTangentSpaceAt n (M ∩ B_r) θ x (span τ)`. So X is integer multiplicity.
7. (Finite boundary mass.) Choose r′ ∈ (r, r₀) and, by (H3), a smooth χ with 0 ≤ χ ≤ 1, χ = 1 on B_{r′}, tsupport χ ⊆ W. Let ω ∈ D^m(ℝ^P) with |ω(x)| ≤ 1 for all x. Then ψ := χω ∈ D^m(U), tsupport ψ ⊆ W, |ψ(x)| ≤ 1, and ψ = ω on the open set B_{r′}, so dψ = dω on B_{r′} ⊇ B_r (the exterior derivative at a point depends only on the germ). Hence, using steps 5, 4 and (H1) for S_r on W,
 ∂X(ω) = X(dω) = ∫_{M∩B_r}θ⟨dω,ξ⟩dH = ∫_{M∩B_r}θ⟨dψ,ξ⟩dH = A₁(dψ) = S_r(ψ) + B₁(ψ) ≤ M_W(S_r) + M_W(∂T).
 Taking the supremum over admissible ω: M(∂X) ≤ M_W(S_r) + M_W(∂T) < ∞.
8. (Conclusion.) r > 0, B_r ⊆ U, and X ∈ D_{m+1}(ℝ^P) is integer multiplicity with M(X) < ∞, M(∂X) < ∞ and X(η) = T(η) for every η ∈ D^{m+1}(U) with tsupport η ⊆ B_r(x₀).

## Key steps

1. T = τ(M,θ,ξ) has locally finite mass, so SlicingTheorem applies with f = |· − x₀|, L = L_W = 1.
2. With R := τ(M ∩ {r₀/2 < f < r₀},θ,ξ) (a restriction of T via the representation (H⌞M, θξ)), the slicing estimate gives M_W(S_r) < ∞ for a.e. r ∈ (r₀/2, r₀); fix such r.
3. Restrictions to the open ball B_r are limits of T(χ_jω), ∂T(χ_jω) with cut-offs, hence unique and mass-bounded: T⌞B_r = τ(M ∩ B_r,θ,ξ) and M((∂T)⌞B_r) ≤ M_W(∂T).
4. X := τ(M ∩ B_r,θ,ξ) on ℝ^P is integer multiplicity (orientation by tangent_locality), has finite mass and agrees with T on forms supported in B_r.
5. With a cut-off χ = 1 near B̄_r, ∂X(ω) = ∂(T⌞B_r)(χω) = S_r(χω) + (∂T⌞B_r)(χω), so M(∂X) ≤ M_W(S_r) + M_W(∂T) < ∞.

## Reference use

### local-project

Queries:
- `cat manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `rg -n '^def |^structure |^abbrev ' project/GMT/Ch06/Contract.lean`
- `cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean (byte-identical)`
- `python3 gmt-compare.py contract_scope / child_modules replay (open MeasureTheory Filter Set Metric; open scoped ENNReal NNReal Topology; namespace GMT.Ch06; open Poincare.SimonGMT.Chapter06; open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasWeightedApproximateTangentSpaceAt); open Poincare.SimonGMT.Chapter01 (dimensionalUpperDensity); noncomputable section; end)`
- `rg -n 'theorem extDeriv_apply' mathlib/Mathlib`
- `rg -n 'theorem Isometry.map_euclideanHausdorffMeasure|theorem EuclideanSpace.euclideanHausdorffMeasure_eq_volume|theorem MeasureTheory.Measure.euclideanHausdorffMeasure_zero' mathlib/Mathlib`
- `rg -n 'theorem hausdorffMeasure_image_le' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n 'def succAboveOrderEmb' mathlib/Mathlib/Order/Fin/Basic.lean`
- `rg -n 'theorem IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero' mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `rg -n 'theorem exists_isSubordinate' mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `rg -n 'structure ContDiffBump' mathlib/Mathlib`
- `rg -n 'theorem norm_fderiv_le_of_lipschitz' mathlib/Mathlib`
- `rg -n 'eq_smul_basis_det' mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `rg -n 'theorem le_restrict_apply|theorem restrict_congr_set|theorem restrict_restrict' mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `rg -n 'theorem setIntegral_eq_integral_of_forall_compl_eq_zero' mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `rg -il 'cauchy.?binet|CauchyBinet' mathlib/Mathlib (no match)`
- `rg -il 'poincare inequality|Poincaré inequality' mathlib/Mathlib (no match)`
- `grep -n 'theorem|def' simongmt Chapter02/BV.lean (IsLocallyBV and lower semicontinuity only; no BV Poincaré or trace inequality)`
- `inspect simongmt Chapter06/{Currents,Mass,CurrentLocalEquality,FormsDuality,Forms,AffineCurrentPushforward}.lean and Chapter03/Rectifiable.lean (GeometricCurrentOn, boundary, massOn, covectorEuclideanNorm, restrictDomain, testFormOnInclusion, simpleNVector, wedgeCovectors_apply_det, exteriorDerivative_apply, blowUpMap, HasWeightedApproximateTangentSpaceAt, CountablyRectifiable)`
- `lake build GMT.Ch06.Submission (scratch /tmp/br_decomp at frozen commit d8d46c9, pinned shared packages)`
- `lake env lean Scratch/FinalCheck.lean (10 frozen child statements, parent assembly, finite_mass_boundary_im from its dependencies; #print axioms)`
- `lake env lean Scratch/ComparatorChallenges.lean (NodeChallenge modules generated by gmt-compare.py child_modules for all 10 statements; 0 errors)`
- `lake build Scratch.AProof (Scratch/TLProof.lean, Scratch/AProof.lean: tangent_locality and restrict_domain_im fully proved; #print axioms)`
- `python3 scan of dag.json lean_name values (no collision with br_* names)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Fin/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/br_decomp/Scratch/FinalCheck.lean`
- `/tmp/br_decomp/Scratch/ComparatorChallenges.lean`
- `/tmp/br_decomp/Scratch/TLProof.lean`
- `/tmp/br_decomp/Scratch/AProof.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) holds the frozen Ch06 contract; Submission.lean is byte-identical to it. Mathlib provides extDeriv_apply (sign (−1)^i with removeNth), isometry invariance of μHE and its identification with Lebesgue measure, Lipschitz image bounds for Hausdorff measure, Fin.succAboveOrderEmb, the open-set fundamental lemma IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (any measure, local integrability only), smooth partitions of unity, ContDiffBump cut-offs, norm_fderiv_le_of_lipschitz and AlternatingMap.eq_smul_basis_det. There is no Cauchy–Binet and no BV Poincaré inequality in Mathlib (no match), and SimonGMT's BV.lean has no Poincaré or trace inequality; hence the children avoid Cauchy–Binet (dual-covector evaluation, operator-norm bounds) and prove the needed BV estimates on boxes directly. SimonGMT supplies restrictDomain, testFormOnInclusion, exteriorDerivativeTestOn, tsupport_exteriorDerivative_subset, boundary_boundary, WeaklyConvergesOn.boundary, massOn_mono, wedgeCovectors_apply_det and countablyRectifiable_iUnion. In a scratch build of the frozen commit, all ten child statements elaborate in the comparator's exact child scope (modules generated by gmt-compare.py); the parent BoundaryRectifiability typechecks from restrict_domain_im, local_to_global_im, finite_mass_boundary_im, localization and the three sibling theorems; finite_mass_boundary_im typechecks from zero_dim_weak_limit, lattice_boundary_im and lattice_approximation; tangent_locality and restrict_domain_im are fully proved with axioms [propext, Classical.choice, Quot.sound]. No br_* name is reserved in the DAG. These checks do not certify the remaining analytic children.
