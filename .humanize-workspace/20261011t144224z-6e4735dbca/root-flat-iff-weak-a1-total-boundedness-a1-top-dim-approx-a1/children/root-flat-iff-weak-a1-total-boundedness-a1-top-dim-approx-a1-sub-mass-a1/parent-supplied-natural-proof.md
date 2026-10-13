# Parent-supplied natural-language proof

- Parent DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1`
- Child DAG node: `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.sub_mass-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the parent proof, step 6 and the first part of step 7. Step 6 shows S := X − Pc is a current. Step 7 shows M(S) ≤ ∫|u − v| dL, because |ω_e| = covectorEuclideanNorm(ω) ≤ 1 for admissible ω.

Notation: n = m + 1, E := Eucl n, L := volume, e_i := EuclideanSpace.single i 1, ω_e(x) := ω(x)(e).

1. (The current S.) Define the linear map S₀ := X.toCurrent − Pc.toCurrent : TestFormOn univ n →ₗ[ℝ] ℝ. If ω_j → 0 (TestFormOnConverges ω 0), then X(ω_j) → 0 and Pc(ω_j) → 0 by the continuity fields of X and Pc. So S₀(ω_j) = X(ω_j) − Pc(ω_j) → 0 − 0 = 0 (Tendsto.sub). Hence S := ⟨S₀, this⟩ ∈ GeometricCurrentOn univ n, and S(ω) = X(ω) − Pc(ω) for all ω (LinearMap.sub_apply).

2. (Top-degree norm.) For α ∈ Covector E n, covectorEuclideanNorm α = |α(e)|. Among I : Fin n → Fin n only I = id is strictly monotone (StrictMono.eq_id), and EuclideanSpace.basisFun (Fin n) ℝ i = e_i. So the defining sum is α(e)², and its square root is |α(e)| (Finset.sum_eq_single, Real.sqrt_sq_eq_abs).

3. (Admissible forms.) Let ω ∈ massAdmissibleOn univ n univ, so covectorEuclideanNorm(ω(x)) ≤ 1 for all x. By step 2, |ω_e(x)| ≤ 1 for all x.
   - ω_e is continuous, hence strongly measurable. So u ω_e and v ω_e are integrable (Integrable.mul_bdd with bound 1), and |u − v| is integrable.
   - Then S(ω) = ∫ u ω_e dL − ∫ v ω_e dL = ∫ (u − v) ω_e dL ≤ ∫ |u − v|·|ω_e| dL ≤ ∫ |u − v| dL. This uses integral_sub and integral_mono with (u − v)ω_e ≤ |u − v|·|ω_e| ≤ |u − v| pointwise.

4. (Mass.) By step 3 and monotonicity of ofReal, for every admissible ω:
   ofReal(S(ω)) ≤ ofReal(∫|u − v| dL) = ∫⁻ ofReal|u − v| dL,
   where the equality is ofReal_integral_eq_lintegral_ofReal (|u − v| ≥ 0 and integrable). By the definitions GeometricCurrentOn.mass and GeometricCurrentOn.massOn,
   S.mass = S.massOn univ = sSup((fun ω => ofReal(S ω)) '' massAdmissibleOn univ n univ).
   So sSup_le (with Set.forall_mem_image) gives S.mass ≤ ∫⁻ ofReal|u − v| dL.

5. S satisfies both assertions: steps 1 and 4. ∎

## Key steps

1. S := X − Pc as a linear map; continuity from Tendsto.sub of the continuity fields of X and Pc.
2. In top degree covectorEuclideanNorm(α) = |α(e)|, so admissible forms satisfy |ω_e| ≤ 1.
3. For admissible ω, S(ω) = ∫(u − v)ω_e ≤ ∫|u − v|.
4. Take the supremum over admissible ω in massOn univ: M(S) ≤ ofReal(∫|u − v|) = ∫⁻ ofReal|u − v|.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (local-project; project d8d46c9587747dee0751a1f780fcafdba16a3886, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/.../project/GMT/Ch06/Contract.lean GMT/Ch06/Contract.lean; cmp Contract.lean Submission.lean; git show 48003458:GMT/Ch06/Submission.lean | cmp (all identical: the node base holds only the frozen contract)`
- `sed -n 120,364p GMT/Ch06/Submission.lean (LatticeFaceIndex, latticeFace, latticeFaceAction, IsLatticeChain, IsIntegerMultiplicity, IsRectifiableTriple, tauAction)`
- `grep -n 'def covectorEuclideanNorm|def massAdmissibleOn|def GeometricCurrentOn.massOn|def GeometricCurrentOn.mass|structure GeometricCurrentOn|def TestFormOnConverges|def GeometricCurrentOn.support|def simpleNVector|def wedgeCovectors|abbrev SimonMultiIndex|instance.*GeometricCurrentOn' simongmt/Poincare/SimonGMT (GeometricCurrentOn has only a Zero instance, no Sub)`
- `grep -n 'def blowUpMap|def HasWeightedApproximateTangentSpaceAt|def CountablyRectifiable|countablyRectifiable_range|CountablyRectifiable.mono' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -rn in local-references mathlib: EuclideanSpace.euclideanHausdorffMeasure_eq_volume, AlternatingMap.eq_smul_basis_det, OrthonormalBasis.det_to_matrix_orthonormalBasis_real, aestronglyMeasurable_iUnion_iff, lintegral_iUnion₀, integral_iUnion_ae, setIntegral_eq_integral_of_forall_compl_eq_zero, lintegral_mul_left_eq_self (to_additive lintegral_add_left_eq_self), lintegral_lintegral_swap, PiLp.volume_preserving_ofLp, volume_Icc_pi, exists_least_of_bdd, tendsto_measure_iUnion_atTop, tendsto_measure_iInter_atTop, ofReal_integral_eq_lintegral_ofReal, setLIntegral_mono', mem_cthickening_of_dist_le, EuclideanSpace.dist_eq, StrictMono.eq_id, Integrable.mul_bdd, lintegral_const_mul', Int.measurable_floor, lintegral_indicator₀ (all found)`
- `python3 scan of dag.json (360 nodes): statuses, frozen lean_statement of siblings fiw_tb_rectifiable_support_null and fiw_tb_translation_estimate, accepted declarations and candidate commits; no lean_name containing 'tda'; git log --all --oneline -S fiw_tb_tda_ (no match)`
- `git cat-file -t 52afef6d 5c248501 eefd7c3e c90a4050 e8e708e4 49ba437c 3d98b187 0561b355 d57bd370 635e85e5 (all present)`
- `git show 635e85e5 -- GMT/Ch06/Submission.lean; tail speculative-process-v3.log of root-boundary-rectifiability-a1-top-dim-lattice-approx-a1 (1060-line single theorem, 178,656 of 200,000 heartbeats)`
- `sed parent-supplied-natural-proof.md of root-boundary-rectifiability-a1-top-dim-lattice-approx-a1 and root-integrality-weak-limits-a1-top-dim-a1 (related top-dimensional arguments; not duplicated)`
- `grep -n in /runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean: def _decompose, def _solve_children, def _existing_lean_name_problem, def _install_parent_supplied_child_handoff, def _overlay prerequisites (runtime.py), def check_source_delta (leaf_verification.py), def ensure (store.py)`
- `verifier/gmt-compare.py contract_scope/child_modules; python3 -I /tmp/tda-tools/check.py (validate_lean_statement on all 8 child types: pass)`
- `lean /tmp/tda-decomp/{Stmts,Comparator,Assembly2,Assembly3,Proto,Proto2}.lean with LEAN_PATH = lake-packages-25730c7c builds + workspace .lake build of d8d46c9 (0 errors; Assembly3 #count_heartbeats 10,901)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1/decomposition-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-top-dim-lattice-approx-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-top-dim-lattice-approx-a1/speculative-process-v3.log`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-top-dim-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/math-wiki/submission-fiw-ims-sc-continuous-of-bound.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/swarm-project.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Group/LIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Int/LeastGreatest.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Preorder/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/Floor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/store.py`
- `/runtime/flows/gmt-claude-52228cbc47b2/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/tda-decomp/Stmts.lean`
- `/tmp/tda-decomp/Comparator.lean`
- `/tmp/tda-decomp/Assembly2.lean`
- `/tmp/tda-decomp/Assembly3.lean`
- `/tmp/tda-decomp/Proto.lean`
- `/tmp/tda-decomp/Proto2.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) has the frozen Ch06 contract, and this node's base commit 48003458 adds no accepted declarations. Neither the project nor SimonGMT contains any of the following, so they become the 8 children:
- the top-dimensional density lemma;
- integer medians;
- the lattice-cube toolkit;
- the chain current;
- the difference-current mass bound;
- the summed Poincaré bound.

API the child proofs use:
- SimonGMT: GeometricCurrentOn (Zero instance only, so S = X − Pc is built from toCurrent subtraction), massOn/mass via massAdmissibleOn and covectorEuclideanNorm, simpleNVector_apply, wedgeCovectors_apply_det, blowUpMap, HasWeightedApproximateTangentSpaceAt, countablyRectifiable_range and CountablyRectifiable.mono.
- Mathlib: every lemma cited in the child proofs was found at the pinned revision.

Accepted declarations, cited only as adaptation pointers (all commits present locally): lpf_pic_current_of_dominated_density (52afef6d), fiw_ims_sc_continuous_of_bound (5c248501), isoperimetric_coord_box_measure (eefd7c3e), fiw_ims_frame_sign (c90a4050).

Scratch checks:
- all 8 child types elaborate in the comparator scope and pass validate_lean_statement;
- the frozen parent type is proved from them plus the two frozen sibling types (10,901 heartbeats; axioms propext, Classical.choice and Quot.sound, plus sorryAx from the stubs only);
- the riskiest child steps compile as prototypes.
