# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.representation_unique-a1`
- Child DAG node: `root.slicing-a1.representation_unique-a1.continuous_to_bounded-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 5–6 of the parent proof: finite measures λ₁ and λ₂, equality on open subsets by monotone convergence, the π–λ theorem, then bounded Borel integrands. Here O is any open set and g₁, g₂ are any integrable functions; the parent uses O = W′ and g_i = g_i^β.

Setting. μ₁, μ₂ are Borel measures on ℝ^P; g_i is μ_i-integrable (i = 1, 2); O ⊆ ℝ^P is open. Hypothesis (H): ∫ φ g₁ dμ₁ = ∫ φ g₂ dμ₂ for every continuous φ with compact support and tsupport φ ⊆ O. Let h : ℝ^P → ℝ be Borel with |h| ≤ C and h = 0 outside O.

0. (Borel representatives.) Each g_i is μ_i-integrable, hence μ_i-a.e. strongly measurable; choose a Borel g̃_i with g̃_i = g_i μ_i-a.e. Then g̃_i is μ_i-integrable, and ∫ f g_i dμ_i = ∫ f g̃_i dμ_i for every function f, because the integrands agree μ_i-a.e. Hypothesis (H) and the conclusion involve only integrals of this form, so it suffices to prove the claim for g̃₁, g̃₂. From now on, assume g₁ and g₂ are Borel.

1. (Two finite measures.) For t ∈ ℝ let t⁺ := max(t, 0) and t⁻ := max(−t, 0), so t = t⁺ − t⁻ and 0 ≤ t^± ≤ |t|. Define Borel measures
 λ₁(B) := ∫_B g₁⁺ dμ₁ + ∫_B g₂⁻ dμ₂ and λ₂(B) := ∫_B g₁⁻ dμ₁ + ∫_B g₂⁺ dμ₂.
 These are sums of measures with nonnegative Borel densities (μ_i.withDensity of ENNReal.ofReal of ±g_i). Both are finite, since λ_i(ℝ^P) ≤ ∫|g₁| dμ₁ + ∫|g₂| dμ₂ < ∞.

2. (Integration identity.) Let f be Borel with |f| ≤ D. Then f is λ₁- and λ₂-integrable, being bounded and measurable on finite measures. Integrating against a sum of measures and against measures with densities gives
 ∫ f dλ₁ = ∫ f g₁⁺ dμ₁ + ∫ f g₂⁻ dμ₂ and ∫ f dλ₂ = ∫ f g₁⁻ dμ₁ + ∫ f g₂⁺ dμ₂.
 All four integrals on the right are finite because |f g_i^±| ≤ D|g_i|. Subtracting and using g_i⁺ − g_i⁻ = g_i gives
 (★) ∫ f dλ₁ − ∫ f dλ₂ = ∫ f g₁ dμ₁ − ∫ f g₂ dμ₂.
 In particular, by (H), ∫ φ dλ₁ = ∫ φ dλ₂ for every continuous φ with compact support and tsupport φ ⊆ O, since such φ are bounded and Borel.

3. (Equality on open subsets of O.) Let V ⊆ O be open; we show λ₁(V) = λ₂(V). For j ≥ 1 let b_j(x) := max(0, min(1, j − |x|)). If V ≠ ℝ^P let a_j(x) := min(1, max(0, j·infDist(x, ℝ^P ∖ V) − 1)); if V = ℝ^P let a_j :≡ 1. Put φ_j := a_j·b_j.
 (i) φ_j is continuous (x ↦ infDist(x, S) is 1-Lipschitz and |·| is continuous), and 0 ≤ φ_j ≤ 1.
 (ii) If φ_j(x) ≠ 0, then |x| < j and, when V ≠ ℝ^P, infDist(x, ℝ^P ∖ V) > 1/j. So φ_j = 0 outside F_j := B̄(0, j) ∩ {x : infDist(x, ℝ^P ∖ V) ≥ 1/j} (F_j := B̄(0, j) if V = ℝ^P). F_j is closed and bounded, hence compact. Moreover F_j ⊆ V, because every point of ℝ^P ∖ V has infDist 0 < 1/j to ℝ^P ∖ V. Hence φ_j has compact support and tsupport φ_j ⊆ F_j ⊆ V ⊆ O.
 (iii) φ_j(x) increases to 1_V(x) for every x. Indeed a_j(x) and b_j(x) are nonnegative and nondecreasing in j. If x ∈ V and V ≠ ℝ^P, then d := infDist(x, ℝ^P ∖ V) > 0, because ℝ^P ∖ V is closed, nonempty and does not contain x; so a_j(x) = 1 once j ≥ 2/d. If V = ℝ^P, a_j(x) = 1. In both cases b_j(x) = 1 once j ≥ |x| + 1. If x ∉ V, then infDist(x, ℝ^P ∖ V) = 0, so a_j(x) = 0 and φ_j(x) = 0.
 By step 2, ∫ φ_j dλ₁ = ∫ φ_j dλ₂ for every j. Since 0 ≤ φ_j ↑ 1_V and λ_i is finite, the monotone convergence theorem (or dominated convergence with dominating function 1) gives ∫ φ_j dλ_i → λ_i(V) for i = 1, 2. Hence λ₁(V) = λ₂(V).

4. (Equality on all Borel subsets of O: π–λ.) Let ν_i(B) := λ_i(B ∩ O), the restriction of λ_i to the Borel set O; ν₁ and ν₂ are finite Borel measures. For every open G ⊆ ℝ^P, G ∩ O is an open subset of O, so ν₁(G) = λ₁(G ∩ O) = λ₂(G ∩ O) = ν₂(G) by step 3; in particular ν₁(ℝ^P) = ν₂(ℝ^P). The open sets form a π-system generating the Borel σ-algebra of ℝ^P. By the π–λ uniqueness theorem for finite measures (Mathlib ext_of_generate_finite with isPiSystem_isOpen), ν₁ = ν₂.

5. (Conclusion.) h is bounded, Borel and vanishes outside O, so ∫ h dλ_i = ∫_O h dλ_i = ∫ h dν_i for i = 1, 2. Step 4 then gives ∫ h dλ₁ = ∫ h dλ₂. Applying (★) with f = h gives ∫ h g₁ dμ₁ = ∫ h g₂ dμ₂. ∎

Formalization note (optional): in Lean, steps 3–4 can be replaced by Radon–Nikodym densities f_i := dλ_i/d(λ₁ + λ₂) together with Mathlib's IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero. Smooth compactly supported functions are continuous, so step 2 gives ∫ ψ·(f₁ − f₂) d(λ₁ + λ₂) = 0 for every such ψ with tsupport ψ ⊆ O. Hence f₁ = f₂ (λ₁ + λ₂)-a.e. on O, and ∫ h dλ₁ = ∫ f₁ h d(λ₁ + λ₂) = ∫ f₂ h d(λ₁ + λ₂) = ∫ h dλ₂.

## Key steps

1. Replace g_i by Borel μ_i-a.e. representatives; no integral changes.
2. Form the finite Borel measures λ₁ = g₁⁺μ₁ + g₂⁻μ₂ and λ₂ = g₁⁻μ₁ + g₂⁺μ₂.
3. Identity (★): ∫ f dλ₁ − ∫ f dλ₂ = ∫ f g₁ dμ₁ − ∫ f g₂ dμ₂ for bounded Borel f; hence λ₁ and λ₂ agree on C_c(O).
4. Continuous cutoffs φ_j ↑ 1_V with tsupport φ_j ⊆ V give λ₁(V) = λ₂(V) for every open V ⊆ O (monotone convergence).
5. π–λ: the finite measures λ₁⌞O and λ₂⌞O agree on the open sets, hence are equal.
6. For bounded Borel h vanishing off O, ∫ h dλ₁ = ∫ h dλ₂; conclude with (★).

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp snapshot project/GMT/Ch06/Contract.lean vs workspace GMT/Ch06/Contract.lean and vs snapshot project/GMT/Ch06/Submission.lean (all byte-identical)`
- `python3 contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') from verifier/gmt-compare.py (child scope: open MeasureTheory Filter Set Metric; open scoped ENNReal NNReal Topology; namespace GMT.Ch06; open Poincare.SimonGMT.Chapter06 ...; noncomputable section; end)`
- `read verifier/gmt-compare.py candidate_inputs/child_modules (only contract + build inputs byte-checked; Submission may add imports) and verifier/lean_contract.py validate_lean_statement`
- `read simongmt Chapter06/{Forms,Currents,FormsDuality,Mass}.lean: Covector, DifferentialForm, IsSmoothForm (ContDiff ℝ ∞), IsTestForm, testFormOnSubmodule/TestFormOn, NVector, SimonMultiIndex, wedgeCovectors, wedgeCovectors_apply_det, euclideanCovectorCoordinate, covectorEuclideanNorm`
- `grep -rn 'IsCompact.exists_cthickening_subset_open|ext_of_generate_finite|isPiSystem_isOpen|integral_withDensity_eq_integral_toReal_smul|isFiniteMeasure_withDensity_ofReal|Module.Basis.ext_alternating|theorem map_perm|monotone_sort|StrictMono.range_inj_of_wellFoundedLT|det_eq_zero_of_column_eq_zero|IsClosed.notMem_iff_infDist_pos|tendsto_integral_of_dominated_convergence|integral_finsetSum' snapshot mathlib/Mathlib`
- `grep -rn 'exists_contMDiffMap_one_nhds_of_subset_interior|Continuous.exists_contDiff_approx|IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero|integral_rnDeriv_smul|integral_toReal_rnDeriv_mul|Measure.integrable_toReal_rnDeriv' snapshot mathlib/Mathlib`
- `python3 scan of dag.json lean_name/status (86 nodes) + grep -rl 'slicing_ru_' nodes/ (no matches); inspected cmb_covector_eq_sum_coord_smul_wedge (same type as child 4, status decomposing) and polyhedral_approx_measure_uniqueness / polyhedral_approx_pairing_expansion (different statements)`
- `lake build GMT.Ch06.Submission (scratch /tmp/ru_split_check from git archive d8d46c9, .lake/packages -> lake-packages-25730c7c)`
- `lake env lean Scratch/Stmts.lean (4 child statements as _root_ comparator targets in the child scope; elaborate)`
- `lake env lean Scratch/AssemblyAx.lean (parent frozen type from the 4 children as axioms + comparator target; #print axioms)`
- `lake env lean Scratch/ChildA.lean, Scratch/ChildC.lean, Scratch/ChildB1.lean, Scratch/ChildB2.lean, Scratch/Full.lean (#print axioms = propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/L1Space/HasFiniteIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Decomposition/IntegralRNDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Manifold/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Fin/Tuple/Sort.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/WellFounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-representation-unique-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-representation-unique-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-polyhedral-approximation-a1-measure-uniqueness-a1/parent-supplied-natural-proof.md`
- `/tmp/ru_split_check/Scratch/Stmts.lean`
- `/tmp/ru_split_check/Scratch/Assembly.lean`
- `/tmp/ru_split_check/Scratch/AssemblyAx.lean`
- `/tmp/ru_split_check/Scratch/ChildA.lean`
- `/tmp/ru_split_check/Scratch/ChildB1.lean`
- `/tmp/ru_split_check/Scratch/ChildB2.lean`
- `/tmp/ru_split_check/Scratch/ChildC.lean`
- `/tmp/ru_split_check/Scratch/Full.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 contract; its Submission is byte-identical, and the comparator byte-checks only the contract and build inputs, so a submission may add Mathlib imports. SimonGMT provides TestFormOn (order-∞ smooth, compact support, tsupport ⊆ U), NVector, SimonMultiIndex, wedgeCovectors with wedgeCovectors_apply_det, and euclideanCovectorCoordinate. It has no coordinate-expansion lemma and no representation-uniqueness lemma, so these become children. Mathlib at the pin provides every tool used: IsCompact.exists_cthickening_subset_open, the smooth Urysohn lemma exists_contMDiffMap_one_nhds_of_subset_interior, Continuous.exists_contDiff_approx, dominated convergence, withDensity integrals and isFiniteMeasure_withDensity_ofReal, ext_of_generate_finite with isPiSystem_isOpen, the Radon–Nikodym integral lemmas, IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero, Module.Basis.ext_alternating, AlternatingMap.map_perm, Tuple.sort and StrictMono.range_inj_of_wellFoundedLT. In a scratch build of the frozen project, all four child statements elaborate in the comparator child scope and pass validate_lean_statement. The parent's exact frozen type is derived from them; besides the four children it uses only [propext, Classical.choice, Quot.sound]. Trial proofs of all four children, under the proposed names, compile together with the parent with no sorry and standard axioms only. The DAG (86 nodes) reserves none of the four names. The identical-type cmb_covector_eq_sum_coord_smul_wedge is not comparator-accepted, so a separate unique name is used.
