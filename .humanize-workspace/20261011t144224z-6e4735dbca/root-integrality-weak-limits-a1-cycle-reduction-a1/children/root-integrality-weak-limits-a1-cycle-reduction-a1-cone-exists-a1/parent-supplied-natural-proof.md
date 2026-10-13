# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1`
- Child DAG node: `root.integrality_weak_limits-a1.cycle_reduction-a1.cone_exists-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. ℝ^P := Eucl P with standard orthonormal basis e_1,…,e_P; D^k(ℝ^P) := TestFormOn univ k (C^∞ k-forms with compact tsupport); D_k(ℝ^P) := GeometricCurrentOn univ k; Λ_k := Covector (ℝ^P) k (continuous alternating k-linear forms) with Mathlib's operator norm ‖·‖; |α| := covectorEuclideanNorm α (the Euclidean coefficient norm used in the mass); (x, v) := Fin.cons x v for x ∈ ℝ^P, v ∈ (ℝ^P)^k; spt := support, M := mass, ⇀ := WeaklyConvergesOn, ∂ := boundary, d := extDeriv; B_r(0), B̄_r(0) are the open and closed balls. For ω ∈ D^{m+1}(ℝ^P), ψ ∈ D^m(ℝ^P) and N ⊆ ℝ^P, say that ψ satisfies the Hω-formula on N if ψ(x)(v) = ∫_0^1 t^m ω(tx)(x, v) dt for all x ∈ N and all v ∈ (ℝ^P)^m. For X ∈ D_m(ℝ^P) and C ∈ D_{m+1}(ℝ^P), Cone(X, C) means: for all ω ∈ D^{m+1}(ℝ^P) and ψ ∈ D^m(ℝ^P), if ψ satisfies the Hω-formula on some open N ⊇ spt X, then C(ω) = X(ψ). (This is verbatim the inline Lean predicate of the statement.) Bump functions: for 0 < r < s there is ζ ∈ C^∞(ℝ^P; ℝ) with 0 ≤ ζ ≤ 1, ζ = 1 on B̄_r(0) and tsupport ζ = B̄_s(0) (a Mathlib ContDiffBump centred at 0 with rIn = r, rOut = s); for such ζ and a C^∞ k-form ψ, ζψ := (x ↦ ζ(x)•ψ(x)) ∈ D^k(ℝ^P) (ContDiff.smul; tsupport(ζψ) ⊆ tsupport ζ, compact).

Source: Part I of the parent proof — definition (0⨯X)(ω) := X(ζ·Hω) with Hω(x) = ∫_0^1 t^m x⌟ω(tx) dt, ζ = 1 near spt X, its independence of ζ by (F2), and item 1 (0⨯X is linear and sequentially continuous) — filled in.

1. (Cut-off.) Let R₀ := max(R, 0), so spt X ⊆ B̄_{R₀}(0). Fix ζ ∈ C^∞(ℝ^P; ℝ) with ζ = 1 on B̄_{R₀+1}(0) and tsupport ζ = B̄_{R₀+2}(0) =: K′ (ContDiffBump at 0 with radii R₀+1 < R₀+2). K′ is compact, and Z_i := sup_x ‖D^iζ(x)‖ < ∞ for each i (D^iζ is continuous and vanishes off K′).
2. (Radial forms.) For ω ∈ D^{m+1}(ℝ^P), ω is a C^∞ (m+1)-form, so iwl_cr_radial_operator (with P, k := m, a := m) gives a C^∞ m-form ψ_ω with (i) ψ_ω(x)(v) = ∫_0^1 t^m ω(tx)(x, v) dt for all x, v, and (iii) the derivative bounds. By (i), ψ_ω(x) is determined for every x (a covector is determined by its values), so ψ_ω is uniquely determined by ω; fix this choice.
3. (Linearity.) For ω, ω′ ∈ D^{m+1} and c ∈ ℝ: ψ_{ω+ω′} = ψ_ω + ψ_{ω′} and ψ_{cω} = cψ_ω. Evaluate at (x, v) with (i) and use linearity of the interval integral; the integrands t ↦ t^m ω(tx)(x, v) are continuous, hence interval integrable on [0,1].
4. (The operator Φ.) Put Φ(ω) := ζψ_ω = (x ↦ ζ(x)•ψ_ω(x)). Then Φ(ω) ∈ D^m(ℝ^P): it is C^∞ (`ContDiff.smul`), and tsupport Φ(ω) ⊆ tsupport ζ = K′ (`tsupport_smul_subset_left`) is compact (and ⊆ univ). By Step 3, Φ : D^{m+1}(ℝ^P) → D^m(ℝ^P) is ℝ-linear.
5. (Sequential continuity of Φ.) Let (ω_l) satisfy TestFormOnConverges ω_l 0: there is a compact K with tsupport ω_l ⊆ K for all l and, for each i, D^iω_l → 0 uniformly on K. Since support(D^iω_l) ⊆ tsupport ω_l ⊆ K (`support_iteratedFDeriv_subset`), δ_l^{(i)} := sup_{y ∈ ℝ^P}‖D^iω_l(y)‖ = sup_{y ∈ K}‖D^iω_l(y)‖ → 0 as l → ∞, for every i. Fix j and put Δ_l := max_{i ≤ j} δ_l^{(i)} (≥ 0, → 0). By (iii) of Step 2 with R := R₀+2 and D := Δ_l: ‖D^iψ_{ω_l}(x)‖ ≤ (R₀+2+i)Δ_l ≤ (R₀+2+j)Δ_l for all i ≤ j and ‖x‖ ≤ R₀+2. By the Leibniz bound for x ↦ ζ(x)•ψ(x) (`norm_iteratedFDeriv_smul_le`, in Mathlib.Analysis.Calculus.ContDiff.Bounds — add this import to Submission.lean, which the comparator permits), for x ∈ K′: ‖D^jΦ(ω_l)(x)‖ ≤ Σ_{i=0}^{j} C(j,i) Z_i ‖D^{j−i}ψ_{ω_l}(x)‖ ≤ (Σ_i C(j,i)Z_i)(R₀+2+j)Δ_l. Hence D^jΦ(ω_l) → 0 uniformly on K′, for every j; together with tsupport Φ(ω_l) ⊆ K′ for all l (and tsupport 0 = ∅), this is TestFormOnConverges (Φ ∘ ω) 0 with the compact set K′ ⊆ univ.
6. (The current.) Define C(ω) := X(Φ(ω)) for ω ∈ D^{m+1}(ℝ^P). C is ℝ-linear (X and Φ are linear), and if TestFormOnConverges ω_l 0 then TestFormOnConverges Φ(ω_l) 0 by Step 5, so C(ω_l) = X(Φ(ω_l)) → 0 by X.continuous'. Thus C ∈ GeometricCurrentOn univ (m+1).
7. (Cone property.) Let ω ∈ D^{m+1}, ψ ∈ D^m and N open with spt X ⊆ N such that ψ(x)(v) = ∫_0^1 t^m ω(tx)(x, v) dt for x ∈ N and all v. Put N′ := N ∩ B_{R₀+1}(0): it is open and contains spt X (spt X ⊆ B̄_{R₀}(0) ⊆ B_{R₀+1}(0)). For x ∈ N′, ζ(x) = 1, so Φ(ω)(x)(v) = ψ_ω(x)(v) = ∫_0^1 t^m ω(tx)(x, v) dt = ψ(x)(v) for all v, i.e. ψ(x) = Φ(ω)(x). Hence the test form ψ − Φ(ω) vanishes on the open set N′, so its support lies in the closed set ℝ^P ∖ N′ and therefore tsupport(ψ − Φ(ω)) ⊆ ℝ^P ∖ N′, which is disjoint from spt X. By isoperimetric_apply_eq_zero_of_disjoint_support and linearity, X(ψ) − X(Φ(ω)) = X(ψ − Φ(ω)) = 0, i.e. X(ψ) = C(ω). So Cone(X, C) holds. ∎

## Key steps

1. Fix a bump ζ = 1 on B̄_{R₀+1}(0) with compact support; for each test form ω take the unique C^∞ radial form ψ_ω of iwl_cr_radial_operator (k = a = m).
2. Φ(ω) := ζψ_ω is a linear map D^{m+1} → D^m; the derivative bounds (iii) and the Leibniz rule give Φ(ω_l) → 0 in the test-form topology whenever ω_l → 0.
3. C(ω) := X(Φ(ω)) is therefore a linear, sequentially continuous current.
4. Any ψ satisfying the Hω-formula on an open N ⊇ spt X agrees with Φ(ω) on the open N ∩ B_{R₀+1}(0) ⊇ spt X, so X(ψ) = X(Φ(ω)) = C(ω) by the reused vanishing lemma.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean GMT/Ch06/Contract.lean; cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean; sha256sum GMT/Ch06/Contract.lean`
- `python3: read nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/{parent-child-handoff,decomposition-v1,decomposition-audit-v1,decomposition-review-receipt-v1}.json`
- `python3: dag.json statuses and frozen lean_statements of iwl_im_closure, iwl_smooth_pushforward, iwl_cycle_reduction, isoperimetric_apply_eq_zero_of_disjoint_support, cmb_abs_apply_le_of_massOn_le, isoperimetric_abs_covector_apply_le, lpf_countably_rectifiable_c1_cover, lpf_rectifiable_area_formula; scan of dag.json and nodes/*/decomposition-v*.json for iwl_cr_* names`
- `rg -n 'theorem exists_partition_approximatesLinearOn_of_hasFDerivWithinAt|theorem MeasurableSet.image_of_continuousOn_injOn|theorem LinearMap.injective_iff_antilipschitz|theorem normDet_sq_eq_det_gram|theorem measurePreserving_piFinSuccAbove|theorem PiLp.volume_preserving_ofLp|theorem PiLp.volume_preserving_toLp|theorem MeasureTheory.Measure.euclideanHausdorffMeasure_zero|theorem hausdorffMeasure_zero_singleton|theorem hausdorffMeasure_apply|theorem exists_measurable_subset_ae_eq|theorem lintegral_prod |theorem Measurable.lintegral_prod_right'|theorem lintegral_iUnion |theorem lintegral_tsum' mathlib/Mathlib (snapshot)`
- `rg -n 'hausdorffMeasure.*prod|area_formula|areaJacobian' mathlib/Mathlib (snapshot)`
- `grep -rln for hasFDerivAt_integral_of_dominated_of_fderiv_le, norm_iteratedFDeriv_le_of_bilinear, norm_iteratedFDeriv_smul_le, alternatizeUncurryFin_curryLeft, extDeriv_extDeriv, tendsto_integral_filter_of_dominated_convergence, integral_integral_swap, euclideanHausdorffMeasure_homothety_image, det_succ_row_zero in snapshot Mathlib`
- `grep -n '^theorem|^def' simongmt Chapter02/{AreaLipschitz,WeightedArea,Area,AreaApproximation,AreaNoninjective}.lean, Chapter03/{Rectifiable,DisjointCover,SubmanifoldCover}.lean, Chapter06/{Currents,Mass,CurrentLocalEquality,Forms}.lean; rg 'pointSlice_isTestForm|iteratedFDeriv_fixedSupportParameterSlice' simongmt`
- `git show 2f3657605e574458d48b2cd837f262ae2f392816:GMT/Ch06/Submission.lean (accepted rectifiability_weighted_tangent_ae, piece construction hpart)`
- `python3 -I /tmp/cr2/scripts/gen.py (verifier gmt-compare.py child_modules + lean_contract.validate_lean_statement); lake env lean /tmp/cr2/gen/*__NodeChallenge.lean`
- `lake env lean /tmp/cr2/Scratch/Assembly.lean, SolutionCheck.lean, LibCheck.lean, JacCheck.lean, SplitCheck.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1/decomposition-review-receipt-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-weighted-tangent-ae-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-weighted-tangent-ae-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-rectifiability-a1-density-comparison-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-isoperimetric-a1-vanish-off-support-a1/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/cr2/scripts/gen.py`
- `/tmp/cr2/Scratch/Assembly.lean`
- `/tmp/cr2/Scratch/SolutionCheck.lean`
- `/tmp/cr2/Scratch/LibCheck.lean`
- `/tmp/cr2/Scratch/JacCheck.lean`
- `/tmp/cr2/Scratch/SplitCheck.lean`

Snapshot: project d8d46c95, Mathlib 25730c7c. Its Ch06 Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean (sha256 ea3ee0dd…853d).

Findings in dag.json:
- The chart-cover and rectifiable-area-formula nodes (lpf_countably_rectifiable_c1_cover, lpf_rectifiable_area_formula) are still speculative-ready, so they cannot be reused.
- No other DAG node supplies a product formula.
- iwl_im_closure and iwl_smooth_pushforward are the parent's frozen sibling dependencies, with the types used in the assembly.
- The reused isoperimetric_apply_eq_zero_of_disjoint_support, cmb_abs_apply_le_of_massOn_le and isoperimetric_abs_covector_apply_le are accepted, with identical types.

Libraries:
- rg in the snapshot Mathlib finds no area formula and no Hausdorff product formula for rectifiable sets; only hausdorffMeasure_pi_real and hausdorffMeasure_prod_real exist.
- The pinned SimonGMT package (lake-packages-25730c7c/simongmt, rev 2b36630) supplies the injective Lipschitz area formula weighted_area_formula_lipschitz_injOn (Chapter02/AreaLipschitz.lean:101). It takes an arbitrary weight, with μHE[finrank E] on the target, volume on the source and J = areaJacobianAt = normDet. It is derived from WeightedArea.lean:76/120. SimonGMT also supplies area_image_compl_regularSet_eq_zero, measurableSet_areaRegularSet and measurable_areaJacobianAt.
- Mathlib supplies exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (Jacobian.lean:255), MeasurableSet.image_of_continuousOn_injOn (Polish/Basic.lean:821), LinearMap.injective_iff_antilipschitz, LinearMap.normDet_sq_eq_det_gram (NormDet.lean:303), measurePreserving_piFinSuccAbove, PiLp.volume_preserving_ofLp/toLp, lintegral_prod, lintegral_iUnion and lintegral_tsum.
- All of these print only propext, Classical.choice and Quot.sound.
- The accepted rectifiability_weighted_tangent_ae (commit 2f36576) already formalizes the same bi-Lipschitz piece construction (`hpart`).
- These inputs give a complete chart-free proof of the product formula.

Lean checks:
- 12 challenge modules and 12 solution resolutions.
- The parent assembly.
- The lift Jacobian identity and the measure-preserving split (standard axioms only).

These checks certify statements, assembly and library inputs, not the remaining analytic proofs. Those were reviewed in natural language; the v1 audit accepted 11 of them, and an independent reviewer accepted the repaired one in this session.

Public citation: Federer, GMT (1969) 3.2.23, cited for this product formula in arXiv:2505.11279.
