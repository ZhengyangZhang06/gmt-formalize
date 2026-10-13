# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.integer_density-a1.const_integer-a1`
- Child DAG node: `root.integrality_weak_limits-a1.integer_density-a1.const_integer-a1.top_integer_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1–2 of the supplied proof of ind_const_multiple_integer, and the computation "X(ω) = ∫_{M″} θ″(y)σ″(y)a(y) dy" of its step 3, carried out here for an arbitrary test form. This is the integer multiplicity case of Simon 2.35 (∗), "T(ω) = ∫ aθ dLⁿ, ω = a dx¹∧⋯∧dxⁿ". It is used with integer-valued θ_j at the end of the Proof of 8.2 (p. 179).

Conventions.
- e := (e_1,…,e_n), s := simpleNVector e, and Hⁿ := μHE[n].
- On ℝⁿ = EuclideanSpace ℝ (Fin n), μHE[n] = volume (EuclideanSpace.euclideanHausdorffMeasure_eq_volume n). Below every μHE[n] is rewritten to volume, written dx.
- U need not be open.

1. Representation. Since X is integer multiplicity, there are M, θ, ξ with:
- IsRectifiableTriple U n M θ ξ;
- for every x ∈ M, θ(x) = k for some k ∈ ℕ;
- X(ω) = tauAction n M θ ξ ω = ∫_M θ(x)·ξ(x)(ω(x)) dx for every ω ∈ TestFormOn U n.
The triple gives:
- M ⊆ U;
- M is volume-null-measurable;
- θ is integrable on M ∩ K for every compact K ⊆ U;
- ξ is AE-strongly measurable for volume.restrict M;
- (orients) for a.e. x ∈ M (with respect to volume.restrict M) there is an orthonormal τ : Fin n → ℝⁿ with ξ(x) = simpleNVector τ or ξ(x) = −simpleNVector τ. The approximate-tangent-space clause is not needed.

2. A volume covector.
- Let vol := wedgeCovectors n (fun j => EuclideanSpace.proj j) (SimonGMT FormsDuality).
- By wedgeCovectors_apply_det, vol(e) = det[proj_i(e_j)] = det 1 = 1, since proj_i(e_j) = 1 if i = j and 0 otherwise.

3. Orientation is ±e_1∧⋯∧e_n.
- Let x be a point of the orients clause, with frame τ.
- By the sibling lemma ind_top_orthonormal_frame_sign (applied to n = m+1 and τ), simpleNVector τ = s or simpleNVector τ = −s.
- The four combinations give ξ(x) = s, −s, −s, or −(−s) = s respectively.
- Hence ξ(x) = s or ξ(x) = −s for a.e. x ∈ M. In Lean, the last case is closed by `ext α; simp`, because simp does not rewrite −(−w) on NVector directly.

4. The sign function. Put σ(x) := ξ(x)(vol).
- If ξ(x) = s, then σ(x) = s(vol) = vol(e) = 1, and for every n-covector α, ξ(x)(α) = α(e) = σ(x)·α(e) (simpleNVector_apply).
- If ξ(x) = −s, then σ(x) = −vol(e) = −1, and ξ(x)(α) = −α(e) = σ(x)·α(e).
- Hence, by step 3, for a.e. x ∈ M: σ(x) = 1 or σ(x) = −1, and ξ(x)(α) = σ(x)·α(e) for every n-covector α.
- σ is the composition of ξ with the continuous linear evaluation map w ↦ w(vol) (ContinuousLinearMap.apply ℝ ℝ vol). So σ is AE-strongly measurable for volume.restrict M (Continuous.comp_aestronglyMeasurable).

5. Definition of u.
- u := M.indicator (fun x => θ(x)·σ(x)), i.e. u = θσ on M and u = 0 off M.

6. Proof of (i).
- Since M is null-measurable, ae_restrict_iff'₀ turns the a.e. statement of step 4 into: for a.e. x ∈ ℝⁿ, x ∈ M ⇒ (σ(x) = 1 ∨ σ(x) = −1).
- Fix such an x.
- If x ∉ M, then u(x) = 0 = ((0 : ℤ) : ℝ).
- If x ∈ M, then θ(x) = k for some k ∈ ℕ, so u(x) = k·σ(x). This equals the integer k when σ(x) = 1 and the integer −k when σ(x) = −1.
- Hence ∃ k : ℤ, u(x) = k for a.e. x.

7. Proof of (ii). Let K ⊆ U be compact.
- θ is integrable on M ∩ K (step 1).
- σ is AE-strongly measurable for volume.restrict (M ∩ K): restrict step 4's measurability using Measure.restrict_mono with M ∩ K ⊆ M.
- |σ| ≤ 1 for a.e. x ∈ M ∩ K, by ae_restrict_of_ae_restrict_of_subset applied to σ = ±1 a.e. on M.
- Hence θ·σ is integrable on M ∩ K (Integrable.mul_bdd with bound 1).
- M is null-measurable also for volume.restrict K (NullMeasurableSet.mono with restrict_le_self).
- So integrable_indicator_iff₀ and Measure.restrict_restrict₀ give: Integrable (M.indicator (θσ)) (volume.restrict K) ⇔ Integrable (θσ) (volume.restrict (M ∩ K)). The right side holds.
- That is, IntegrableOn u K volume.

8. Proof of (iii). Let ω ∈ TestFormOn U n.
- By step 1 (with μHE[n] = volume), X(ω) = ∫_M θ(x)·ξ(x)(ω(x)) dx.
- By step 4 with α := ω(x), θ(x)·ξ(x)(ω(x)) = θ(x)σ(x)·ω(x)(e) for a.e. x ∈ M. So X(ω) = ∫_M θ(x)σ(x)·ω(x)(e) dx (integral_congr_ae on volume.restrict M).
- For every x, u(x)·ω(x)(e) = M.indicator (fun y => θ(y)σ(y)·ω(y)(e)) (x), by cases x ∈ M or x ∉ M.
- M is null-measurable for volume.restrict U. So integral_indicator₀ and Measure.restrict_restrict₀ give ∫_U u(x)·ω(x)(e) dx = ∫_{M ∩ U} θσ·ω(e) dx.
- M ∩ U = M because M ⊆ U, so this equals ∫_M θσ·ω(e) dx.
- Hence X(ω) = ∫_U u(x)·ω(x)(e) dx.

9. Steps 5–8 give u with (i), (ii) and (iii). ∎

## Key steps

1. Unpack IsIntegerMultiplicity X: triple (M, θ, ξ) with θ ∈ ℕ on M and X = tauAction n M θ ξ; rewrite μHE[n] = volume.
2. From orients and ind_top_orthonormal_frame_sign: ξ(x) = ±simpleNVector e for a.e. x ∈ M.
3. σ := ξ(·)(vol), with vol := wedgeCovectors n (EuclideanSpace.proj ·) and vol(e) = 1, is AE-strongly measurable; a.e. on M, σ = ±1 and ξ(x)(α) = σ(x)·α(e).
4. u := M.indicator(θσ) is integer-valued a.e. (ae_restrict_iff'₀, θ ∈ ℕ on M, u = 0 off M).
5. u is integrable on each compact K ⊆ U: θ is integrable on M ∩ K and |σ| ≤ 1, so θσ is integrable there (Integrable.mul_bdd); then use integrable_indicator_iff₀ and restrict_restrict₀.
6. X(ω) = ∫_M θσ·ω(e) = ∫_U u·ω(e) (integral_congr_ae, integral_indicator₀, M ⊆ U).

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-const-integer-a1/{parent-child-handoff.json,parent-supplied-plan.md,parent-supplied-natural-proof.md}`
- `cat local-references/197bdd4b88278494/manifest.json (local-project; project d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `diff -q local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean; diff -q against workspace GMT/Ch06/Contract.lean (all identical)`
- `python3 scans of dag.json (383 nodes): siblings under root.integrality_weak_limits-a1.integer_density-a1; constancy-a1 branch statements/statuses; statements containing simpleNVector | Orthonormal | Matrix.det | ae_eq_zero | 'fun i => EuclideanSpace.single i (1 : ℝ)'; top_dim nodes; collision check for ind_top_orthonormal_frame_sign, ind_top_dim_integer_density, ind_top_form_density_ae_unique`
- `git show c90a40505abdbff33b9174acf9b20037eb2cb2a1 (accepted fiw_ims_frame_sign result commit: helper layout of child Submission.lean)`
- `rg -n "theorem (IsOpen\.ae_eq_zero_of_integral_contDiff_smul_eq_zero|EuclideanSpace\.euclideanHausdorffMeasure_eq_volume|AlternatingMap\.eq_smul_basis_det|OrthonormalBasis\.det_to_matrix_orthonormalBasis_real|locallyIntegrableOn_iff|IntegrableOn\.mul_continuousOn|integrableOn_iff_integrable_of_support_subset|setIntegral_eq_integral_of_forall_compl_eq_zero|Integrable\.mul_bdd|tsupport_smul_subset_left|HasCompactSupport\.smul_right)" local-references/197bdd4b88278494/mathlib/Mathlib`
- `rg -n -F -e "theorem LinearIndependent.span_eq_top_of_card_eq_finrank'" -e "theorem integrable_indicator_iff₀" -e "theorem integral_indicator₀" -e "theorem restrict_restrict₀ " -e "theorem ae_restrict_iff'₀" -e "protected theorem coe_mk (hon : Orthonormal" local-references/197bdd4b88278494/mathlib/Mathlib; rg -n image_eq_zero_of_notMem_tsupport; rg -n basisFun_apply Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `grep -n basisOfOrthonormalOfCardEqFinrank|span_eq_top_of_card_eq_finrank' .lake/packages/mathlib/Mathlib (Nonempty requirement check)`
- `grep -n '^def \|^theorem \|^abbrev \|^structure ' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/{Forms,Currents,FormsDuality,Mass,CurrentLocalEquality,FormSupNorm,WedgeForms,Representation,CurrentDistributionEquivalence}.lean; rg -n 'wedgeCovectors_apply_det|def wedgeCovectors|def simpleNVector|simpleNVector_apply' FormsDuality.lean`
- `sed -n 2440,2475p book/chapter-06.txt (end of printed Proof of 8.2, p. 179); grep -n 2.35 book/chapter-06.txt and sed -n 606,640p (Remark 2.35 (∗))`
- `python3 -I validate.py verifier/lean_contract.py stmts.json (3 statements OK); read verifier/gmt-compare.py contract_scope/child_modules`
- `lake env lean /tmp/cimi-decomp-7f3a/{Stmts,Assembly,ProofA,ProofB,ProofC,Probe,Full}.lean (#print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-const-integer-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-const-integer-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-const-integer-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/LpSpace/Indicator.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/cimi-decomp-7f3a/Stmts.lean`
- `/tmp/cimi-decomp-7f3a/Assembly.lean`
- `/tmp/cimi-decomp-7f3a/ProofA.lean`
- `/tmp/cimi-decomp-7f3a/ProofB.lean`
- `/tmp/cimi-decomp-7f3a/ProofC.lean`
- `/tmp/cimi-decomp-7f3a/Full.lean`
- `/tmp/cimi-decomp-7f3a/py/stmts.json`

Snapshot and project:
- The snapshot is project d8d46c95 with Mathlib 25730c7c.
- Its Contract.lean and Submission.lean are byte-identical to each other and to the workspace contract.
- The contract imports FormsDuality and Mass from SimonGMT. These provide simpleNVector and simpleNVector_apply, wedgeCovectors with wedgeCovectors_apply_det (giving vol(e) = det 1 = 1), and TestFormOn: IsTestForm (ContDiff ℝ ∞ plus HasCompactSupport) with tsupport ⊆ U.

Mathlib supplies every step of the child proofs:
- EuclideanSpace.euclideanHausdorffMeasure_eq_volume
- AlternatingMap.eq_smul_basis_det and OrthonormalBasis.det_to_matrix_orthonormalBasis_real
- LinearIndependent.span_eq_top_of_card_eq_finrank' (no Nonempty requirement), OrthonormalBasis.mk/coe_mk, EuclideanSpace.basisFun_apply
- IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (needs LocallyIntegrableOn) and locallyIntegrableOn_iff (IsLocallyClosed)
- IntegrableOn.mul_continuousOn, integrableOn_iff_integrable_of_support_subset, setIntegral_eq_integral_of_forall_compl_eq_zero, Integrable.mul_bdd
- the null-measurable lemmas integrable_indicator_iff₀, integral_indicator₀, Measure.restrict_restrict₀, ae_restrict_iff'₀
- tsupport_smul_subset_left, HasCompactSupport.smul_right, image_eq_zero_of_notMem_tsupport

DAG:
- The accepted fiw_ims_frame_sign has a different type; it is only an optional route to child A.
- No accepted node states the top-dimensional density representation or uniqueness. fiw_tb_tda_density (U = univ, finite mass) and constancy_topForm_scalar_reduction are decomposing.
- The proposed names ind_top_orthonormal_frame_sign, ind_top_dim_integer_density and ind_top_form_density_ae_unique have no DAG or library hits.

Book: the printed end of the Proof of 8.2 (p. 179) writes top-dimensional currents as ∫ aθ_j dLⁿ (Simon 2.35 (∗)) and concludes "θ ≡ θ(x) … thus θ(x) ∈ ℤ". This matches children B and C.

Scratch Lean (all axioms: propext, Classical.choice, Quot.sound):
- The 3 statements validate and elaborate.
- The parent assembly compiles.
- A, C, and B (from A) are fully proved.
- The combined Full.lean compiles with 0 errors and 0 sorry.
