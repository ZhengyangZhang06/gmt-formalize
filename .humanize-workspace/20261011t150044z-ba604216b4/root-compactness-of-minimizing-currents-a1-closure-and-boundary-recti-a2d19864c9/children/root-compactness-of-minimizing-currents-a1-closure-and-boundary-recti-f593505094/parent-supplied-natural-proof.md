# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.plane_integer-a1.plane_stokes-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.plane_integer-a1.plane_stokes-a1.extderiv_coords-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the supplied proof of cbr_cipi_plane_halfspace_stokes, together with the closed-embedding part of its step 1.

Notation:
- ω := φ, viewed as a map ℝ^P → Covector(ℝ^P, d).
- ι(x) := Σ_j x_j v_j.
- For i ∈ Fin (d+1): G_i(y) := ω(y)(removeNth i v).
- So g_i(x) = G_i(ι x).

1. (Data of a test form.) φ ∈ TestFormOn univ d means IsTestForm ω ∧ tsupport ω ⊆ univ.
   - IsTestForm ω = IsSmoothForm ω ∧ HasCompactSupport ω.
   - IsSmoothForm ω = ContDiff ℝ ∞ ω, where ∞ = (⊤ : ℕ∞), i.e. all finite orders.
   So ω is C^∞ and has compact support.

2. (ι is a closed linear embedding.) Take ι := Fintype.linearCombination ℝ v. It is a linear map (Fin (d+1) → ℝ) → ℝ^P with ι(x) = Σ_j x_j v_j (Fintype.linearCombination_apply).
   - An orthonormal family is linearly independent (Orthonormal.linearIndependent).
   - So ι is injective (LinearIndependent.fintypeLinearCombination_injective), i.e. ker ι = ⊥ (LinearMap.ker_eq_bot).
   - The domain is finite-dimensional, so ι is continuous (LinearMap.toContinuousLinearMap).
   - Being injective with finite-dimensional domain, ι is a closed embedding (LinearMap.isClosedEmbedding_of_injective).

3. (The functions G_i.) Fix i and put u := removeNth i v.
   - Evaluation α ↦ α(u) is a continuous linear map Covector(ℝ^P, d) → ℝ (ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ u).
   - Hence G_i = (evaluation at u) ∘ ω is C^∞: a continuous linear map is C^∞, and composing with the C^∞ map ω gives ContDiff.comp.
   - Evaluation sends 0 to 0, so G_i has compact support because ω does (HasCompactSupport.comp_left).

4. (Proof of (i).) By the formula for ι in step 2, g_i(x) = ω(Σ_j x_j v_j)(removeNth i v) = G_i(ι x) for every x, so g_i = G_i ∘ ι.
   - ι is a continuous linear map, hence C^∞, so g_i is C^∞ (ContDiff.comp).
   - Therefore g_i is C¹ (ContDiff.of_le, since 1 ≤ ∞).
   - G_i has compact support (step 3) and ι is a closed embedding (step 2), so g_i has compact support (HasCompactSupport.comp_isClosedEmbedding).

5. (Chain rule.) Fix z ∈ ℝ^{d+1}.
   - G_i is C^∞, so it is differentiable at ι z with Fréchet derivative DG_i(ι z).
   - The continuous linear map ι has derivative ι at z (ContinuousLinearMap.hasFDerivAt).
   - By the chain rule (HasFDerivAt.comp), g_i = G_i ∘ ι has derivative DG_i(ι z) ∘ ι at z, so Dg_i(z) = DG_i(ι z) ∘ ι (HasFDerivAt.fderiv).
   - Hence Dg_i(z)(e_i) = DG_i(ι z)(ι e_i).
   - Since (e_i)_j = 1 for j = i and 0 otherwise, ι(e_i) = Σ_j (e_i)_j v_j = v_i (Pi.single_apply, Finset.sum_ite_eq).
   Therefore Dg_i(z)(e_i) = DG_i(ι z)(v_i).

6. (Proof of (ii).) ω is C^∞, hence differentiable at ι z. The coordinate formula for the exterior derivative (exteriorDerivative_apply) gives
   dω(ι z)(v) = Σ_{i ∈ Fin (d+1)} (−1 : ℤ)^i • D[y ↦ ω(y)(removeNth i v)](ι z)(v_i) = Σ_i (−1 : ℤ)^i • DG_i(ι z)(v_i).
   - An integer n acts on ℝ by multiplication by (n : ℝ) (zsmul_eq_mul).
   - ((−1 : ℤ)^i : ℝ) = (−1 : ℝ)^i.
   - Rewrite each summand by step 5 (Finset.sum_congr).
   This gives dω(ι z)(v) = Σ_i (−1 : ℝ)^i · Dg_i(z)(e_i). Since ι z = Σ_j z_j v_j, this is (ii). ∎

## Key steps

1. ι(x) = Σ_j x_j v_j = Fintype.linearCombination ℝ v x is linear and injective (orthonormal ⇒ linearly independent), hence a continuous closed embedding (finite-dimensional domain).
2. G_i(y) = φ(y)(removeNth i v) = (evaluation CLM) ∘ φ is C^∞ with compact support, and g_i = G_i ∘ ι.
3. Proof of (i): g_i is C^∞, hence C¹, and has compact support (HasCompactSupport.comp_isClosedEmbedding).
4. Chain rule: Dg_i(z)(e_i) = DG_i(ι z)(ι e_i) = DG_i(ι z)(v_i).
5. Proof of (ii): exteriorDerivative_apply gives dφ(ι z)(v) = Σ (−1)^i • DG_i(ι z)(v_i) = Σ (−1 : ℝ)^i · Dg_i(z)(e_i) (zsmul_eq_mul).

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
