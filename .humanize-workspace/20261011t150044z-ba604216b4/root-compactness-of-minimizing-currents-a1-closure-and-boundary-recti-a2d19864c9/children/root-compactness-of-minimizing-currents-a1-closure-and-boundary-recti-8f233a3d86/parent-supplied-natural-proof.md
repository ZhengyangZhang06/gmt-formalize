# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.plane_integer-a1.plane_stokes-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.plane_integer-a1.plane_stokes-a1.halfspace_boundary-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1, 3, 4, 5 and 6 of the supplied proof of cbr_cipi_plane_halfspace_stokes. The parent's siblings plane_measure (P1) and halfspace_ftc (P2) are replaced by the hypotheses (PM) and (FTC), which are their exact frozen statements. Step 2 of that proof is the sibling extderiv_coords.

Notation:
- ω := φ, viewed as a map ℝ^P → Covector(ℝ^P, d).
- V₀ := span(range v).
- H_t := {y : ⟨y, v_0⟩ < t}.
- L_t := {y : y − t v_0 ∈ span(range(Fin.tail v))}.
- F(y) := dω(y)(v).
- ι(z) := Σ_j z_j v_j.
- g_i(x) := ω(Σ_j x_j v_j)(removeNth i v).

Introduce (PM), (FTC), P, d, v (orthonormal), φ and t.

1. (Coordinates for dω.) Apply the sibling extderiv_coords (Submission.cbr_cipi_plane_extDeriv_coords) to P, d, v, φ:
   - every g_i is C¹ with compact support;
   - for every z, F(ι z) = Σ_i (−1)^i Dg_i(z)(e_i).

2. (Continuity of the integrands.)
   - dω is C^∞ (exteriorDerivative_isTestForm applied to IsTestForm ω).
   - So F = (evaluation at v) ∘ dω is continuous, because evaluation, ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ v, is a continuous linear map.
   - Likewise y ↦ ω(y)(Fin.tail v) is continuous.
   - Continuous functions are a.e. strongly measurable for every measure.

3. (Parametrising V₀.) Apply (PM)(i) with m := d+1, w := v, a := 0:
   Measure.map ι₀ L^{d+1} = H^{d+1}⌞{y : y − 0 ∈ V₀}, where ι₀(z) := 0 + Σ_i z_i v_i.
   - Since y − 0 = y, the set {y : y − 0 ∈ V₀} equals the set V₀.
   - Hence ι₀_*(L^{d+1}) = H^{d+1}⌞V₀.
   - ι₀ is continuous, hence measurable.

4. (Left side in coordinates.)
   - H_t is open, being a strict inequality between the continuous map y ↦ ⟨y, v_0⟩ and the constant t. Hence H_t is measurable.
   - By Set.inter_comm and Measure.restrict_restrict (H_t measurable): H^{d+1}⌞(V₀ ∩ H_t) = (H^{d+1}⌞V₀)⌞H_t = (ι₀_* L^{d+1})⌞H_t.
   - By setIntegral_map (H_t measurable, F a.e. strongly measurable, ι₀ measurable): ∫_{V₀∩H_t} F dH^{d+1} = ∫_{ι₀⁻¹(H_t)} F(ι₀ z) dz.
   - Orthonormality gives ⟨Σ_i z_i v_i, v_0⟩ = z_0 (Orthonormal.inner_left_fintype; conjugation is the identity on ℝ). So ι₀⁻¹(H_t) = {z : z_0 < t}.
   - ι₀(z) = ι(z) (zero_add).
   Hence LHS = ∫_{z_0<t} F(ι z) dz.

5. (Termwise integration.) By step 1, F(ι z) = Σ_i (−1)^i Dg_i(z)(e_i). For each i:
   - z ↦ Dg_i(z)(e_i) is continuous: g_i is C¹, so Dg_i is continuous (ContDiff.continuous_fderiv), and we apply it to the constant vector e_i.
   - It has compact support (HasCompactSupport.fderiv_apply).
   - Hence it is Lebesgue integrable (Continuous.integrable_of_hasCompactSupport), as is its product with the constant (−1)^i and its restriction to {z_0 < t}.
   By integral_finset_sum (now integral_finsetSum) and integral_const_mul:
   LHS = Σ_i (−1)^i ∫_{z_0<t} Dg_i(z)(e_i) dz.

6. (Apply (FTC).) Split off i = 0 (Fin.sum_univ_succ).
   - For i = k.succ with k ∈ Fin d: the first part of (FTC), applied to d, g_{k.succ}, t (C¹ with compact support by step 1) and the index k.succ ≠ 0 (Fin.succ_ne_zero), gives ∫_{z_0<t} Dg_{k.succ}(z)(e_{k.succ}) dz = 0. So all these terms vanish.
   - For i = 0: (−1)^0 = 1, and the second part of (FTC) applied to g_0 gives ∫_{z_0<t} Dg_0(z)(e_0) dz = ∫_{ℝ^d} g_0(Fin.cons t z′) dz′.
   Hence LHS = ∫_{ℝ^d} g_0(Fin.cons t z′) dz′.

7. (Right side in coordinates.)
   - Fin.tail v = v ∘ Fin.succ = (v_1, …, v_d) is orthonormal (Orthonormal.comp with the injective Fin.succ).
   - Apply (PM)(i) with m := d, w := Fin.tail v, a := t • v_0: Measure.map j L^d = H^d⌞L_t, where j(z′) := t v_0 + Σ_k z′_k (Fin.tail v)_k. The map j is continuous, hence measurable.
   - The right side is the integral of y ↦ ω(y)(Fin.tail v) against H^d⌞L_t = j_*L^d.
   - So by integral_map (j measurable, integrand continuous by step 2): RHS = ∫_{ℝ^d} ω(j z′)(Fin.tail v) dz′.

8. (Identification and conclusion.) Let z′ ∈ ℝ^d.
   - removeNth 0 v = Fin.tail v (Fin.removeNth_zero).
   - Σ_j (Fin.cons t z′)_j v_j = t v_0 + Σ_k z′_k v_{k.succ} = j(z′), by Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ and (Fin.tail v)_k = v_{k.succ}.
   Hence g_0(Fin.cons t z′) = ω(j z′)(Fin.tail v) for every z′. The integrals in steps 6 and 7 therefore coincide, and LHS = RHS. ∎

## Key steps

1. extderiv_coords: every g_i = φ(Σ x_j v_j)(removeNth i v) is C¹ with compact support, and dφ(ι z)(v) = Σ_i (−1)^i Dg_i(z)(e_i).
2. (PM) with a = 0, w = v gives ι_*(L^{d+1}) = H^{d+1}⌞V₀. With restrict_restrict, setIntegral_map and ⟨ι z, v_0⟩ = z_0: ∫_{V₀∩H_t} dφ(v) = ∫_{z_0<t} dφ(ι z)(v) dz.
3. Integrate termwise (each ∂_i g_i is continuous with compact support, hence integrable): LHS = Σ_i (−1)^i ∫_{z_0<t} ∂_i g_i.
4. (FTC): the terms with i ≠ 0 vanish and the i = 0 term equals ∫ g_0(Fin.cons t z′) dz′.
5. (PM) with a = t v_0, w = Fin.tail v and integral_map: RHS = ∫ φ(t v_0 + Σ z′_k v_{k+1})(Fin.tail v) dz′.
6. removeNth 0 v = Fin.tail v and ι(Fin.cons t z′) = t v_0 + Σ z′_k v_{k+1}, so the two coordinate integrals agree.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean && cmp <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `rg -n 'theorem extDeriv_pullback|theorem extDeriv_apply|theorem fintypeLinearCombination_injective|theorem isClosedEmbedding_of_injective|theorem setIntegral_map|theorem inner_left_fintype|theorem setIntegral_eq_of_subset_of_forall_sdiff_eq_zero|theorem setIntegral_eq_zero_of_forall_eq_zero|theorem HasCompactSupport.fderiv_apply|theorem fderiv_apply' <snapshot>/mathlib/Mathlib (hits in MeasureTheory/Integral/Bochner/Set.lean, Analysis/Calculus/FDeriv/Const.lean, Analysis/Calculus/DifferentialForm/Basic.lean)`
- `rg -il stokes <snapshot>/mathlib/Mathlib <snapshot>/project (only Mathlib/Analysis/BoxIntegral/DivergenceTheorem.lean; no plane or half-space Stokes lemma)`
- `rg -l 'cbr_cipi_plane_extDeriv_coords|cbr_cipi_plane_halfspace_boundary|cbr_cipi_plane_boundary_zero' <snapshot> (no match)`
- `lake env lean /tmp/cipi-ps-decomp/lean/Sigs.lean: #check of Orthonormal.inner_left_fintype, ContinuousAlternatingMap.apply, HasCompactSupport.comp_isClosedEmbedding, LinearMap.isClosedEmbedding_of_injective, Fintype.linearCombination_apply, LinearIndependent.fintypeLinearCombination_injective, setIntegral_map, integral_map, Measure.restrict_restrict, setIntegral_eq_of_subset_of_forall_diff_eq_zero, setIntegral_eq_zero_of_forall_eq_zero, HasCompactSupport.fderiv_apply, Continuous.integrable_of_hasCompactSupport, integral_finset_sum, Fin.removeNth_zero, image_eq_zero_of_notMem_tsupport, exteriorDerivative_apply, tsupport_exteriorDerivative_subset, Submodule.closed_of_finiteDimensional, IsCompact.exists_bound_of_continuousOn, Submodule.mem_span_range_iff_exists_fun, Orthonormal.comp, ContDiff.continuous_fderiv (all reachable after import GMT.Ch07.Submission)`
- `sed -n 1,160p lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean and sed -n 100,200p .../Chapter06/Currents.lean (IsSmoothForm = ContDiff ℝ ∞, IsTestForm, TestFormOn, exteriorDerivative = extDeriv, exteriorDerivative_apply, exteriorDerivative_isTestForm, tsupport_exteriorDerivative_subset)`
- `python3 -I scans of dag.json: candidate lean names unused; nodes whose lean_statement contains removeNth or exteriorDerivative+Submodule.span (cbr_ci_constant_cycle_planes, cmr_df_*, dgcr_bwd_*, cmcs_wn_*, cbr_ci_cp_*: none with these types, no plane/half-space Stokes lemma); frozen types of cbr_cipi_affine_plane_measure, cbr_cipi_halfspace_partial_integral and cbr_cipi_plane_halfspace_stokes byte-compared with the embedded hypotheses and the assembled parent (identical)`
- `grep/sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py: _decompose (depth >= max_depth stops splitting), _solve_children, _existing_lean_name_problem, _overlay_accepted_children (prerequisites = node.children + node.depends_on only), _wait_for_accepted_dependencies`
- `git show {9fc696be8f,fb5be2a6d3,ed3a6a23d0,db9f39016b}:GMT/Ch07/Submission.lean | grep -c 'theorem Submission.<parent dependency>' (0 each: a parent's prerequisites are absent at its children's dispatch base)`
- `python3 -I prefix.py: gmt-compare.contract_scope(Contract.lean, GMT.Ch07.main_theorem) -> import GMT.Ch07.Submission; open Filter Function Set MeasureTheory Metric; open scoped ENNReal Topology; namespace GMT.Ch07; open Poincare.SimonGMT.Chapter06; open Poincare.SimonGMT.Chapter03 (...); noncomputable section; end`
- `lake env lean /tmp/cipi-ps-decomp/lean/{Stmts,ChildA,ChildB,ChildC,E2E,E2E2,Comparator}.lean (exit 0, 0 errors; #print axioms of the three children: propext, Classical.choice, Quot.sound)`
- `python3 -I verifier/lean_contract.py validate_lean_statement on the three child statements (ok)`
- `sed -n 130,150p and 205,222p book/chapter-06.txt (Simon 6.1.11 definition of d; 6.2.3 boundary via Stokes)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/BoxIntegral/DivergenceTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-a2d19864c9/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-93e0ab338f/decomposition-v1.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/cipi-ps-decomp/lean/Sigs.lean`
- `/tmp/cipi-ps-decomp/lean/E2E2.lean`
- `/tmp/cipi-ps-decomp/lean/Comparator.lean`

The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean (project b4d606db, Mathlib 25730c7c). Every library lemma the three child proofs use exists and is reachable from import GMT.Ch07.Submission. Neither Mathlib, SimonGMT nor the DAG has a plane or half-space Stokes lemma or a coordinate formula for d along a parametrised plane, so all three children are new and their names are unused. Children of this node do not see the parent's prerequisites, so the frozen plane_measure and halfspace_ftc types (byte-identical to dag.json) enter halfspace_boundary as hypotheses. In scratch Lean all three child types elaborate in the comparator scope, each child is proved as one Submission.* theorem using only propext, Classical.choice and Quot.sound, and the frozen parent type follows from the children and the two sibling declarations by a one-line assembly.
