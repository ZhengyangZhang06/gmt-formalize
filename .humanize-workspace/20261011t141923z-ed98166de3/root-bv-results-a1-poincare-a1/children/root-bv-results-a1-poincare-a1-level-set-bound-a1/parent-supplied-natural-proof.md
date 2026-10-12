# Parent-supplied natural-language proof

- Parent DAG node: `root.bv_results-a1.poincare-a1`
- Child DAG node: `root.bv_results-a1.poincare-a1.level_set_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: this is step B5 of the parent's complete argument (Section B of the supplied proof of Simon 2.7). Section B replaces Simon's constants β(σ) → β by the mean ū, then transfers to β using the level-set hypothesis 2.7(*). The argument of B5 never uses that ū is a mean, so it is stated here for an arbitrary constant c.

Notation. ℝⁿ = EuclideanSpace ℝ (Fin n), μ = volume (Lebesgue measure), μ_U := μ.restrict U. Put I := ∫⁻_U ‖u − c‖ₑ dμ ∈ [0,∞], a := ‖c − β‖ₑ = ofReal|c − β| ∈ [0,∞) and f(x) := ‖u(x) − c‖ₑ. Because u is a.e.-measurable for μ_U, so is f (AEMeasurable.sub_const, then .enorm). All arithmetic is in [0,∞], so the cases I = ∞ or μ(U) = ∞ need no separate treatment.

1. Triangle inequality. For every x, ‖u(x) − β‖ₑ = ‖(u(x) − c) + (c − β)‖ₑ ≤ f(x) + a (enorm_add_le). By monotonicity of the lintegral, additivity against the measurable constant a (lintegral_add_right with measurable_const) and ∫⁻_U a = a·μ(U) (setLIntegral_const):
   ∫⁻_U ‖u − β‖ₑ ≤ I + a·μ(U).
2. Claim: a·(ofReal θ·μ(U)) ≤ I. By Markov's inequality for the a.e.-measurable f (mul_meas_ge_le_lintegral₀): a·μ_U{x : a ≤ f(x)} ≤ ∫⁻ f dμ_U = I. Since U is measurable, μ_U(S) = μ(S ∩ U) for every set S, measurable or not (Measure.restrict_apply'). Also {x : β ≤ u(x)} ∩ U = {x ∈ U : β ≤ u(x)}, and similarly for {u ≤ β}.
   (a) Case c ≤ β. If β ≤ u(x), then u(x) − c ≥ β − c ≥ 0, so f(x) = |u(x) − c| ≥ β − c = |c − β| = a. Hence {x : β ≤ u(x)} ⊆ {x : a ≤ f(x)}. Measure monotonicity holds for outer measures, so the level set need not be measurable. Using the hypothesis (the min is ≤ its first argument):
       a·ofReal θ·μ(U) ≤ a·μ{x ∈ U : β ≤ u(x)} = a·μ_U{x : β ≤ u(x)} ≤ a·μ_U{x : a ≤ f(x)} ≤ I.
   (b) Case β < c. If u(x) ≤ β, then c − u(x) ≥ c − β > 0, so f(x) ≥ c − β = a. Hence {x : u(x) ≤ β} ⊆ {x : a ≤ f(x)}, and the same chain, now using the second argument of the min, gives a·ofReal θ·μ(U) ≤ I.
3. Since θ > 0, ofReal(θ⁻¹)·ofReal(θ) = ofReal(θ⁻¹θ) = ofReal 1 = 1 (ENNReal.ofReal_mul with θ⁻¹ ≥ 0). Hence a·μ(U) = ofReal(θ⁻¹)·(a·(ofReal θ·μ(U))) ≤ ofReal(θ⁻¹)·I by step 2.
4. From steps 1 and 3, ∫⁻_U ‖u − β‖ₑ ≤ I + ofReal(θ⁻¹)·I = (1 + ofReal(θ⁻¹))·I = ofReal(1 + θ⁻¹)·I. The last equality is ENNReal.ofReal_add (1 ≥ 0, θ⁻¹ ≥ 0) with ofReal 1 = 1. This is the claim. ∎

Formalization note: every Mathlib fact cited above is in the import closure of the frozen GMT.Ch02.Submission; the whole argument was checked in Lean as a single appended theorem with no added imports.

## Key steps

1. Integrate the pointwise triangle inequality ‖u−β‖ₑ ≤ ‖u−c‖ₑ + ‖c−β‖ₑ over U: ∫⁻_U‖u−β‖ₑ ≤ I + ‖c−β‖ₑ·μ(U), where I = ∫⁻_U‖u−c‖ₑ.
2. Apply Markov (mul_meas_ge_le_lintegral₀) to ‖u−c‖ₑ under μ.restrict U. The level set {β ≤ u} (if c ≤ β) or {u ≤ β} (if β < c) lies inside {‖u−c‖ₑ ≥ ‖c−β‖ₑ}, and restrict_apply' holds for measurable U. Together with the hypothesis this gives ‖c−β‖ₑ·ofReal θ·μ(U) ≤ I.
3. Multiply by ofReal(θ⁻¹), using ofReal(θ⁻¹)·ofReal θ = 1: ‖c−β‖ₑ·μ(U) ≤ ofReal(θ⁻¹)·I. Conclude with I + ofReal(θ⁻¹)·I = ofReal(1+θ⁻¹)·I.

## Reference use

### local-project

Queries:
- `python3 -I: read nodes/root-bv-results-a1-poincare-a1/parent-child-handoff.json; list lean_name/lean_statement/status/depends_on of every dag.json node and of nodes/root-bv-results-a1/decomposition-v1.json subproblems`
- `grep -n 'BV\|bvVariation\|IsBVOn\|namespace\|^open\|^import' GMT/Ch02/Contract.lean; sed -n 230,280p GMT/Ch02/Contract.lean; grep -n '2.7\|Poincar\|errat' GMT/Ch02/README.md; sed -n 620,662p book/chapter-02.txt`
- `rg -n "theorem (tendsto_setIntegral_of_monotone|tendsto_setLIntegral_zero|mul_meas_ge_le_lintegral₀|le_restrict_apply|restrict_apply'|enorm_integral_le_lintegral_enorm|tendsto_measure_iUnion_atTop|setLIntegral_const|lintegral_inter_add_diff)" mathlib/Mathlib`
- `rg -n 'lintegral_comp_smul|lintegral_add_left_eq_self|lintegral_add_right_eq_self|map_addHaar_smul|addHaar_smul|integral_comp_smul' mathlib/Mathlib`
- `rg -n 'theorem (le_infDist|infDist_le_dist_of_mem|infDist_zero_of_mem|continuous_infDist_pt|lipschitz_infDist_pt)|notMem_iff_infDist_pos|infDist_pos' mathlib/Mathlib/Topology/MetricSpace`
- `rg -n 'theorem diam_mono|theorem diam_closedBall|theorem dist_le_diam_of_mem|IsBounded.measure_lt_top' mathlib/Mathlib`
- `rg -n "theorem (setLIntegral_iUnion_of_directed|setLIntegral_mono'|lintegral_const_mul'|lintegral_lintegral_swap|le_opENorm_of_le|setIntegral_const|finrank_euclideanSpace_fin)|lintegral_prod_right'" mathlib/Mathlib`
- `rg -n 'theorem (integral_normed|nonneg_normed|support_normed_eq|hasCompactSupport_normed|contDiff_normed|continuous_normed)' mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean; rg -n 'contDiff_convolution_left|hasContDiffBump_of_innerProductSpace' mathlib/Mathlib`
- `python3 -I gen_checks.py (verifier gmt-compare.py contract_scope/child_modules + lean_contract.validate_lean_statement), then lean NodeChallenge_00..03.lean against a scratch olean of the frozen GMT.Ch02.Submission`
- `lean ChildA.lean ChildB.lean ChildC.lean ChildL.lean AssemblyCheck.lean PoincareKids.lean PoincareKidsOneImport.lean NodeSolution_00..04.lean CitedNames.lean (#check of all 56 cited names) with #print axioms`
- `leaf-shape check: _recursive_lean/leaf_verification.check_source_delta on four single-theorem Submission candidates; lean -o each candidate, then NodeSolution (exact Submission.X) against it`
- `grep -rl for poincare_level_set_lintegral_le, convex_poincare_smooth_lintegral_le, convex_open_exists_inner_exhaustion, mean_oscillation_lintegral_le_of_approx in the run directory, simongmt/Poincare and mathlib/Mathlib`
- `cmp of the 18 cited snapshot mathlib files with lake-packages-25730c7c/mathlib (git HEAD 25730c7c759d108ef87ab70af2342a196760f79d); cmp workspace GMT/Ch02/Contract.lean with snapshot project/GMT/Ch02/Contract.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Group/LIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/BumpFunction/InnerProduct.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Normed/Operator/NNNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/GMT/Ch02/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-6e6a457c9391/_recursive_lean/leaf_verification.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-bv-results-a1-poincare-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-bv-results-a1/decomposition-v1.json`
- `/tmp/poincare-decomp-8oly3q/checks/NodeChallenge_00.lean`
- `/tmp/poincare-decomp-8oly3q/checks/NodeChallenge_03.lean`
- `/tmp/poincare-decomp-8oly3q/checks/PoincareKids.lean`
- `/tmp/poincare-decomp-8oly3q/checks/PoincareKidsOneImport.lean`
- `/tmp/poincare-decomp-8oly3q/checks/NodeSolution_04.lean`
- `/tmp/poincare-decomp-8oly3q/checks/CitedNames.lean`
- `/tmp/poincare-decomp-8oly3q/leafcheck/L1/src/GMT/Ch02/Submission.lean`

Snapshot and frozen sources:
- The snapshot Contract.lean is byte-identical to the workspace contract. IsBVOn (line 76) bundles IsOpen U, IntegrableOn u U volume and bvVariationOn u U < ⊤, and BVPoincare (line 258) is the selected type.
- README line 94 ('u ∈ BV(U) includes u ∈ L¹(U)') is the only 2.7 reading.
- book/chapter-02.txt lines 627–661 contain the printed proof. Its 'usual Poincaré inequality for smooth functions [GT01]' is the child convex_poincare_smooth_lintegral_le.
- All 18 cited snapshot Mathlib files are identical to the build package at 25730c7c.

Mathlib supplies every lemma the children use:
- mul_meas_ge_le_lintegral₀;
- Measure.restrict_apply' (valid for any second set);
- map_addHaar_smul, lintegral_map, lintegral_smul_measure and lintegral_add_left_eq_self;
- intervalIntegral.integral_eq_sub_of_hasDerivAt;
- lintegral_lintegral_swap and Measurable.lintegral_prod_right';
- tendsto_measure_iUnion_atTop and tendsto_setIntegral_of_monotone;
- setLIntegral_iUnion_of_directed (no measurability needed);
- Metric.le_infDist, IsClosed.notMem_iff_infDist_pos, dist_le_diam_of_mem, diam_mono and diam_closedBall.

What Mathlib lacks:
- There is no lintegral_comp_smul. The dilation identity is derived from map_addHaar_smul.
- There is no Poincaré, level-set or convex-exhaustion lemma, so the four children are genuine new obligations.

Import closure:
- All 56 cited names resolve after importing only GMT.Ch02.Submission.
- ContDiffBump.normed, which only the parent needs, requires import Mathlib.Analysis.Calculus.BumpFunction.Normed. With that single extra import the parent assembly compiles.

Verification:
- The four statements pass validate_lean_statement and the contract_scope replay, and the generated NodeChallenge modules compile.
- Complete proofs of all four children compile in a combined module, and also as single-theorem leaves that pass check_source_delta. `exact Submission.X` depends only on propext, Classical.choice and Quot.sound.
- BVPoincare assembles from the four children and the exact DAG types of bv_mollifier_tendsto_L1 and bv_mollifier_fderiv_lintegral_le. Its axioms are the standard ones plus sorryAx, and sorryAx comes only from those two placeholders.

Names: none of the four names occurs in dag.json, any decomposition, the run directory, SimonGMT or Mathlib.
