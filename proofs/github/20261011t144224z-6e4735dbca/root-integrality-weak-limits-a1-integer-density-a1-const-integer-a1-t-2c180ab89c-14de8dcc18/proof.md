# Parent-supplied natural-language proof

- Parent DAG node: `root.integrality_weak_limits-a1.integer_density-a1.const_integer-a1`
- Child DAG node: `root.integrality_weak_limits-a1.integer_density-a1.const_integer-a1.top_density_unique-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 3–4 of the supplied proof of ind_const_multiple_integer (testing with ω = a·vol, then the fundamental lemma IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero). Here they are applied to the difference u − v instead of g = c·1_U − 1_{M″}θ″σ″. This is the identification "θ ≡ θ(x) in B₁ⁿ(0)" at the end of Simon's Proof of 8.2 (p. 179), where top-dimensional currents act by ω = a dx¹∧⋯∧dxⁿ ↦ ∫ aθ dLⁿ (Simon 2.35 (∗)).

Notation: e := (e_1,…,e_n), and dx is volume on ℝⁿ.

1. A volume covector.
- Let vol := wedgeCovectors n (fun j => EuclideanSpace.proj j), from SimonGMT FormsDuality.
- By wedgeCovectors_apply_det, vol(e) = det[proj_i(e_j)]_{i,j}.
- proj_i(e_j) = (single j 1)_i is 1 if i = j and 0 otherwise. So the matrix is the identity and vol(e) = det 1 = 1.

2. Local integrability.
- For each compact K ⊆ U, x ↦ u(x) − v(x) is integrable on K (IntegrableOn.sub of the two hypotheses).
- U is open, hence locally closed (IsOpen.isLocallyClosed).
- So by locallyIntegrableOn_iff, u − v is locally integrable on U: LocallyIntegrableOn (fun x => u x − v x) U volume.

3. Reduction to the fundamental lemma.
- Mathlib's IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (on ℝⁿ with the volume measure) states: let f be locally integrable on the open set U, and suppose ∫ a(x)•f(x) dx = 0 (integral over all of ℝⁿ) for every a : ℝⁿ → ℝ with ContDiff ℝ ∞ a, HasCompactSupport a and tsupport a ⊆ U. Then ∀ᵐ x, x ∈ U → f(x) = 0.
- Apply it with f := u − v, using step 2. Steps 4–7 verify the integral condition for a fixed such a; step 8 concludes.

4. The test form a·vol.
- Fix a : ℝⁿ → ℝ with ContDiff ℝ ∞ a, HasCompactSupport a and tsupport a ⊆ U.
- Define ω(x) := a(x)•vol.
- ω is C^∞ (ContDiff.smul of a and the constant map, contDiff_const).
- ω has compact support (HasCompactSupport.smul_right).
- tsupport ω ⊆ tsupport a ⊆ U (tsupport_smul_subset_left).
- Hence ω ∈ TestFormOn U n, and ω(x)(e) = a(x)·vol(e) = a(x) for every x, by step 1.

5. The hypothesis.
- Applied to this ω, and rewriting ω(x)(e) = a(x), the hypothesis reads ∫_U u(x)a(x) dx = ∫_U v(x)a(x) dx.

6. Integrability.
- Let w ∈ {u, v} and K := tsupport a. K is compact (HasCompactSupport a) and K ⊆ U.
- Then w is integrable on K. Since a is continuous, x ↦ w(x)a(x) is integrable on K (IntegrableOn.mul_continuousOn).
- Its support is contained in support a ⊆ tsupport a = K. So it is integrable on all of ℝⁿ (integrableOn_iff_integrable_of_support_subset), in particular on U.

7. The integral vanishes.
- If x ∉ U then x ∉ tsupport a, so a(x) = 0 (image_eq_zero_of_notMem_tsupport) and a(x)•(u(x) − v(x)) = 0.
- Hence ∫ a•(u − v) dx = ∫_U a•(u − v) dx (setIntegral_eq_integral_of_forall_compl_eq_zero).
- Pointwise, a(x)•(u(x) − v(x)) = u(x)a(x) − v(x)a(x).
- Using step 6 (integral_sub), ∫_U (u·a − v·a) dx = ∫_U u·a dx − ∫_U v·a dx, which is 0 by step 5.
- Therefore ∫ a(x)•(u(x) − v(x)) dx = 0.

8. Conclusion.
- Steps 4–7 verify the hypothesis of step 3 for every admissible a.
- So for a.e. x: x ∈ U ⇒ u(x) − v(x) = 0, i.e. u(x) = v(x) (sub_eq_zero). This is ∀ᵐ x, x ∈ U → u x = v x. ∎

## Key steps

1. vol := wedgeCovectors n (fun j => EuclideanSpace.proj j) satisfies vol(e) = det 1 = 1 (wedgeCovectors_apply_det).
2. u − v is integrable on compacts of the open set U, hence LocallyIntegrableOn U (locallyIntegrableOn_iff, IsOpen.isLocallyClosed).
3. For a ∈ C_c^∞ with tsupport a ⊆ U, ω := a•vol ∈ TestFormOn U n with ω(x)(e) = a(x), so the hypothesis gives ∫_U u·a = ∫_U v·a.
4. u·a and v·a are integrable (IntegrableOn.mul_continuousOn on tsupport a, then support ⊆ tsupport a), and a = 0 off U, so ∫ a•(u − v) = ∫_U u·a − ∫_U v·a = 0.
5. IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero applied to u − v gives u = v a.e. on U.

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
