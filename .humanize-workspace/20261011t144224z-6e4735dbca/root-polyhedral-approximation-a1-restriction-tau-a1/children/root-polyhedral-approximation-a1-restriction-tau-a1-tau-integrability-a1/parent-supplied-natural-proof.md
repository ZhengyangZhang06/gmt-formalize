# Parent-supplied natural-language proof

- Parent DAG node: `root.polyhedral_approximation-a1.restriction_tau-a1`
- Child DAG node: `root.polyhedral_approximation-a1.restriction_tau-a1.tau_integrability-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

These are steps 1 and 2(b) of the parent proof. Write Hⁿ := μHE[n] and ν := Hⁿ⌞M. Fix a compact K ⊆ U and an n-covector c.

1. (Unit simple n-vectors.) Let τ : Fin n → ℝ^P be orthonormal.
   - By definition, simpleNVector τ is LinearMap.mkContinuous of the evaluation functional α ↦ α(τ), with bound constant ∏_i ‖τ_i‖ ≥ 0.
   - So ‖simpleNVector τ‖ ≤ ∏_i ‖τ_i‖ (LinearMap.mkContinuous_norm_le).
   - Orthonormality gives ‖τ_i‖ = 1 for every i (Orthonormal.norm_eq_one), so the product is 1. This includes the empty product when n = 0.
   Hence ‖simpleNVector τ‖ ≤ 1, and also ‖−simpleNVector τ‖ = ‖simpleNVector τ‖ ≤ 1.

2. (A.e. bound for ξ.) By the orients field of the triple, for ν-a.e. x there is an orthonormal τ with ξ(x) = simpleNVector τ or ξ(x) = −simpleNVector τ. By step 1, ‖ξ(x)‖ ≤ 1 for ν-a.e. x. For such x, the operator-norm inequality gives |ξ(x)(c)| ≤ ‖ξ(x)‖·‖c‖ ≤ ‖c‖.

3. (Reduction to Hⁿ⌞(M∩K).)
   - K is compact, hence closed and Borel measurable.
   - Therefore ν⌞K = (Hⁿ⌞M)⌞K = Hⁿ⌞(K∩M) = Hⁿ⌞(M∩K) (Measure.restrict_restrict).
   - Integrability on K with respect to ν means integrability with respect to ν⌞K. So it suffices to show that x ↦ θ(x)·ξ(x)(c) is Hⁿ⌞(M∩K)-integrable.
   - Since M∩K ⊆ M, Hⁿ⌞(M∩K) ≤ Hⁿ⌞M = ν (Measure.restrict_mono).

4. (θ.) The integrableOn field of the triple, applied to the compact K ⊆ U, says that θ is Hⁿ-integrable on M∩K, i.e. Hⁿ⌞(M∩K)-integrable.

5. (ξ(·)(c).)
   - The map w ↦ w(c) on n-vectors is continuous linear (ContinuousLinearMap.apply).
   - ξ is a.e.-strongly measurable for ν (aestronglyMeasurable field), so x ↦ ξ(x)(c) is a.e.-strongly measurable for ν. By step 3 it is then a.e.-strongly measurable for the smaller measure Hⁿ⌞(M∩K) (AEStronglyMeasurable.mono_measure).
   - The bound |ξ(x)(c)| ≤ ‖c‖ from step 2 holds ν-a.e., hence Hⁿ⌞(M∩K)-a.e. (ae_mono).

6. (Product.) An integrable function times an a.e.-strongly measurable, a.e.-bounded function is integrable (Integrable.mul_bdd). Applying this to θ (step 4) and x ↦ ξ(x)(c) (step 5) shows that x ↦ θ(x)·ξ(x)(c) is Hⁿ⌞(M∩K)-integrable. By step 3, this is integrability on K with respect to ν. ∎

## Key steps

1. For orthonormal τ, ‖±simpleNVector τ‖ ≤ ∏‖τ_i‖ = 1 (mkContinuous bound).
2. The orients field gives ‖ξ(x)‖ ≤ 1, hence |ξ(x)(c)| ≤ ‖c‖, for Hⁿ⌞M-a.e. x.
3. Since K is measurable, (Hⁿ⌞M)⌞K = Hⁿ⌞(M∩K) ≤ Hⁿ⌞M.
4. θ is Hⁿ⌞(M∩K)-integrable by the triple's integrableOn field.
5. ξ(·)(c) is a.e.-strongly measurable (continuous evaluation of ξ) and a.e. bounded by ‖c‖ for Hⁿ⌞(M∩K).
6. Integrable.mul_bdd gives integrability of θ·ξ(·)(c) on K for Hⁿ⌞M.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp snapshot project/GMT/Ch06/Contract.lean and project/GMT/Ch06/Submission.lean against workspace GMT/Ch06/Contract.lean (byte-identical)`
- `python3 contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') from verifier/gmt-compare.py (namespace GMT.Ch06; open MeasureTheory Filter Set Metric; open scoped ENNReal NNReal Topology; open Poincare.SimonGMT.Chapter06/Chapter03/Chapter01 selections)`
- `read simongmt Chapter06 Forms.lean (Covector, DifferentialForm, IsSmoothForm = ContDiff ℝ ∞, IsTestForm), Currents.lean (testFormOnSubmodule, TestFormOn, GeometricCurrentOn), FormsDuality.lean (NVector, SimonMultiIndex, simpleNVector via mkContinuous with bound ∏‖v i‖, wedgeCovectors, euclideanCovectorCoordinate), Mass.lean (covectorEuclideanNorm)`
- `grep -n 'theorem exists_contMDiffMap_zero_one_of_isClosed|theorem exists_contMDiffMap_one_nhds_of_subset_interior' mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `grep IsCompact.exists_cthickening_subset_open|IsCompact.cthickening|closure_thickening_subset_cthickening|self_subset_thickening|cthickening_mono in Topology/MetricSpace/Thickening.lean`
- `grep Integrable.bdd_mul|Integrable.mul_bdd (MeasureTheory/Function/L1Space/Integrable.lean); IntegrableOn.congr_fun|IntegrableOn.integrable_of_forall_notMem_eq_zero (MeasureTheory/Integral/IntegrableOn.lean); integral_finsetSum (MeasureTheory/Integral/Bochner/Basic.lean); restrict_restrict (MeasureTheory/Measure/Restrict.lean)`
- `grep mkContinuous_norm_le (Analysis/Normed/Operator/Basic.lean); Orthonormal.norm_eq_one; contMDiff_iff_contDiff (Geometry/Manifold/ContMDiff/NormedSpace.lean); Continuous.bounded_above_of_compact_support; instContinuousEvalConst (Topology/Algebra/Module/Alternating/Topology.lean); tsupport_smul_subset_left|HasCompactSupport.smul_right (Topology/Algebra/Support.lean); notation μHE (Geometry/Euclidean/Volume/Measure.lean)`
- `python3 scan of dag.json (107 nodes) for lean_name polyhedral_approx_rt_* and for statements containing 'IntegrableOn (fun x => v x c)' or 'θ x * ξ x'; grep -rl 'polyhedral_approx_rt_' dag.json nodes/ GMT/ simongmt/Poincare (no match)`
- `inspect nodes/root-polyhedral-approximation-a1/decomposition-v1.json and decomposition-audit-v1.json (exact uncle types), nodes/root-slicing-a1-representation-unique-a1/decomposition-v1.json and decomposition-audit-v1.json (slicing_ru_integrableOn_apply: α-equivalent type, status decomposing)`
- `grep -n '2.7|2.9|3.1 Definition' book/chapter-06.txt and book/sources/chapter-06-source.txt (no printed proof of T⌞A = τ(M∩A,θ,ξ))`
- `lean_contract.validate_lean_statement on both child statements (pass)`
- `git archive d8d46c9 -> /tmp/rt_decomp_check; LEAN_PATH=<pinned package oleans> lean -R . -o .lake/build/lib/lean/GMT/Ch06/Submission.olean GMT/Ch06/Submission.lean`
- `lean Scratch/Stmts.lean (2 child statements + exact parent type as _root_ comparator targets in the child scope; elaborate)`
- `lean Scratch/Assembly.lean (exact parent type from the 2 uncles + 2 children as axioms, no sorry)`
- `lean Scratch/Children.lean; lean Scratch/ChildrenNoImport.lean (complete trial proofs; #print axioms = propext, Classical.choice, Quot.sound)`
- `lean Scratch/Full.lean (uncles as axioms, children and parent proved; parent target axioms = standard + polyhedral_approx_measure_uniqueness + polyhedral_approx_pairing_expansion; child targets = standard only)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Manifold/ContMDiff/NormedSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormSupNorm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-06-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-polyhedral-approximation-a1-restriction-tau-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-polyhedral-approximation-a1-restriction-tau-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-polyhedral-approximation-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-polyhedral-approximation-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-polyhedral-approximation-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-polyhedral-approximation-a1/speculative-prompt-v1.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-representation-unique-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-representation-unique-a1/decomposition-audit-v1.json`
- `/tmp/rt_decomp_check/Scratch/Stmts.lean`
- `/tmp/rt_decomp_check/Scratch/Assembly.lean`
- `/tmp/rt_decomp_check/Scratch/Children.lean`
- `/tmp/rt_decomp_check/Scratch/ChildrenNoImport.lean`
- `/tmp/rt_decomp_check/Scratch/Full.lean`

The snapshot pins project d8d46c95 and Mathlib 25730c7c. It holds the frozen Ch06 contract, and its Submission is byte-identical to that contract.

The contract supplies IsRectifiableTriple (fields integrableOn, aestronglyMeasurable, orients), tauAction, IsMeasureRepresentation and IsRestriction. SimonGMT supplies TestFormOn (smooth of order ∞, compact support, tsupport ⊆ U), NVector and simpleNVector (defined by mkContinuous with bound ∏‖τ_i‖), wedgeCovectors and euclideanCovectorCoordinate. Neither the contract nor SimonGMT contains a local-integrability lemma for representations or for τ(M,θ,ξ); these become the two children.

Mathlib at the pin provides every tool the children use: IsCompact.exists_cthickening_subset_open, the smooth Urysohn lemma exists_contMDiffMap_zero_one_of_isClosed, contMDiff_iff_contDiff, closure_thickening_subset_cthickening, IsCompact.cthickening, IntegrableOn.congr_fun, LinearMap.mkContinuous_norm_le, Orthonormal.norm_eq_one, Measure.restrict_restrict and Integrable.mul_bdd. It also provides what the parent assembly uses: integral_finsetSum, Integrable.bdd_mul, IntegrableOn.integrable_of_forall_notMem_eq_zero, continuous_eval_const for ContinuousAlternatingMap, HasCompactSupport.comp_left and tsupport_comp_subset.

Lean results in a scratch build of the frozen commit:
- Both child statements pass validate_lean_statement and elaborate in the comparator child scope.
- The exact frozen parent type compiles from the two uncles (exact frozen types) and the two children, with no sorry.
- Complete trial proofs of both children compile with only propext, Classical.choice and Quot.sound, and need no extra import.
- In the combined file, the parent target depends only on standard axioms plus its two declared dependencies.

The proposed names are unused across the DAG, the node files and the sources. The α-equivalent slicing_ru_integrableOn_apply is not comparator-accepted, so it is not reused.
