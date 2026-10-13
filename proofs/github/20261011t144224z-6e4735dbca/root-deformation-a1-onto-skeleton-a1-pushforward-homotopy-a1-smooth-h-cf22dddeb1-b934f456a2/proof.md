# Parent-supplied natural-language proof

- Parent DAG node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_homotopy-a1.affine_estimate-a1`
- Child DAG node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_homotopy-a1.affine_estimate-a1.affine_homotopy_proper-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2–3 of the supplied proof of dph_sh_affine_estimate (closedness of the cylinder and properness of G; Simon Ch. 6, 2.25/2.27), stated for an arbitrary closed set S in place of spt X. Notation as in the statement. Put e := EuclideanSpace.equiv (Fin (m+1)) ℝ and e′ := EuclideanSpace.equiv (Fin m) ℝ.

1. (Continuity and the shape of the cylinder.) t = tL := (ContinuousLinearMap.proj 0) ∘L e and tl = tlL := e′.symm ∘L (ContinuousLinearMap.pi (j ↦ ContinuousLinearMap.proj j.succ)) ∘L e are continuous linear maps. Both identities hold definitionally, because Fin.tail q = (j ↦ q j.succ). Therefore:
   - G = F₀∘tlL + tL·(F₁∘tlL − F₀∘tlL) is continuous, being built from compositions, differences, scalar products and sums of continuous maps;
   - cyl(S) = tL⁻¹([0,1]) ∩ tlL⁻¹(S).

2. (The set is closed.) Fix a compact K ⊆ ℝ^{m′}. K is closed, because compact subsets of the Hausdorff space ℝ^{m′} are closed (IsCompact.isClosed). So G⁻¹(K) is closed. Since [0,1] and S are closed and tL, tlL are continuous, cyl(S) is closed. Hence C := G⁻¹(K) ∩ cyl(S) is closed.

3. (A compact superset.)
   - K_s := cthickening s K is compact, because ℝ^{m′} is a proper metric space (IsCompact.cthickening; no sign condition on s is needed).
   - By hypothesis P := F₀⁻¹(K_s) ∩ S is compact, so [0,1] × P is compact (isCompact_Icc.prod).
   - The map Φ : ℝ × ℝ^m → ℝ^{m+1}, Φ(τ, x) := cons(τ, x) = e.symm (Fin.cons τ (e′ x)), is continuous. It is the continuous linear map (τ, x) ↦ Fin.cons τ (e′ x) (ContinuousLinearMap.finCons of fst and e′ ∘L snd) followed by the continuous e.symm.
   - Therefore Q := Φ([0,1] × P) is compact (IsCompact.image).

4. (C ⊆ Q.) Let y ∈ C and put τ := t(y) and x := tl(y). Then G(y) ∈ K, τ ∈ [0,1] and x ∈ S.
   (a) Φ(τ, x) = y. Indeed e′ x = e′ (e′.symm (Fin.tail (e y))) = Fin.tail (e y) and τ = (e y) 0. So Fin.cons τ (e′ x) = Fin.cons ((e y) 0) (Fin.tail (e y)) = e y (Fin.cons_self_tail), and e.symm (e y) = y.
   (b) F₀(x) ∈ K_s. By definition G(y) = F₀(x) + τ·(F₁(x) − F₀(x)), so F₀(x) − G(y) = −(τ·(F₁(x) − F₀(x))). Hence dist(F₀(x), G(y)) = ‖τ·(F₁(x) − F₀(x))‖ = |τ|·‖F₁(x) − F₀(x)‖ = τ·dist(F₁(x), F₀(x)), using τ ≥ 0 and dist_eq_norm. Since τ ≤ 1 and dist ≥ 0, this is ≤ 1·dist(F₁(x), F₀(x)) ≤ s, by the hypothesis at x ∈ S. As G(y) ∈ K, Metric.mem_cthickening_of_dist_le gives F₀(x) ∈ cthickening s K = K_s.
   Hence x ∈ P, so (τ, x) ∈ [0,1] × P and y = Φ(τ, x) ∈ Q.

5. (Conclusion.) By steps 2–4, C is a closed subset of the compact set Q, so C is compact (IsCompact.of_isClosed_subset). Since K was an arbitrary compact set, G⁻¹(K) ∩ cyl(S) is compact for every compact K ⊆ ℝ^{m′}. ∎

## Key steps

1. t and tl are continuous linear, so G is continuous and cyl(S) = t⁻¹[0,1] ∩ tl⁻¹(S) is closed; hence G⁻¹(K) ∩ cyl(S) is closed for compact (hence closed) K.
2. Q := cons([0,1] × (F₀⁻¹(cthickening s K) ∩ S)) is compact: the cthickening of a compact set is compact, the properness hypothesis applies, and (τ,x) ↦ cons(τ,x) is continuous.
3. For y ∈ G⁻¹(K) ∩ cyl(S): y = cons(t y, tl y) by Fin.cons_self_tail, and dist(F₀(tl y), G y) = t(y)·dist(F₁(tl y), F₀(tl y)) ≤ s, so F₀(tl y) ∈ cthickening s K and y ∈ Q.
4. A closed subset of a compact set is compact.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `python3 -I verifier/gmt-compare.py contract_scope(GMT/Ch06/Contract.lean, GMT.Ch06.main_theorem) -> open MeasureTheory Filter Set Metric / open scoped ENNReal NNReal Topology / namespace GMT.Ch06 / open Poincare.SimonGMT.Chapter06 / open ...Chapter03 (CountablyRectifiable HasWeightedApproximateTangentSpaceAt) / open ...Chapter01 (dimensionalUpperDensity) / noncomputable section / end; diff Contract.lean Submission.lean (identical)`
- `grep -n '^structure|^def|^abbrev|^theorem' .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/{Forms,Currents,Mass,CurrentLocalEquality}.lean: Covector, DifferentialForm, TestFormOn = testFormOnSubmodule (IsTestForm ∧ tsupport ⊆ U), GeometricCurrentOn, support = U \ zeroRegion, isOpen_zeroRegion, massOn, mass = massOn U, covectorEuclideanNorm, covectorEuclideanNorm_zero/_nonneg`
- `python3 -I over dag.json: selected node (depth 5, decomposing); lean_statement/status of mass_bound, compatible_form, slice_forms (accepted) and slice_comparison, interior_bound (decomposing); regex scan of all statements for cthickening | Fin.tail | fderiv ℝ (fun y | homotop | IsCompact (.*⁻¹' -> precedent iwl_cr_ci_cone_map, no straight-line-homotopy lemma`
- `git show 61b7d3fe17a438a487bdf3a56eb93a01e6c7accd:GMT/Ch06/Submission.lean (accepted iwl_cr_ci_cone_map: p₀, π as continuous linear maps, Φ-values by rfl, HasFDerivAt.smul, compContinuousLinearMap_apply, Fin.comp_cons)`
- `grep -n -i 'proper|ContDiff|affine|straight|F₀|cthickening' nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1/parent-supplied-natural-proof.md (Parts 4.3, 5.1: G_ij C^∞ and proper on [0,1]×spt X; 6.11: ĥ_σ C^∞ and proper)`
- `rg -n 'theorem norm_integral_le_of_norm_le_const|theorem mem_cthickening_of_dist_le|IsCompact.cthickening|theorem compContinuousLinearMap_apply|theorem comp_cons|theorem cons_self_tail|theorem HasFDerivAt.smul|lemma ofLp_single|abbrev EuclideanSpace.single|abbrev EuclideanSpace.equiv|theorem IsCompact.of_isClosed_subset|lemma uIoc_of_le' local-references/197bdd4b88278494/mathlib/Mathlib; cmp of 8 snapshot files with .lake/packages/mathlib (all identical)`
- `lake env lean Probe.lean / Probe2.lean: #check intervalIntegral.norm_integral_le_of_norm_le_const, Metric.mem_cthickening_of_dist_le, IsCompact.cthickening, image_eq_zero_of_notMem_tsupport, ContinuousAlternatingMap.compContinuousLinearMap_apply, Fin.comp_cons, ContinuousLinearMap.opNorm_le_bound, pow_le_pow_left₀, HasFDerivAt.fun_add/fun_sub/fun_smul, ContDiff.differentiable (n ≠ 0), ContDiff.fun_smul, Fin.cons_self_tail, ContinuousLinearMap.finCons, IsCompact.of_isClosed_subset, Set.uIoc_of_le`
- `lake env lean /tmp/dph_sh_ae_split/lean/AllStmts.lean (2 children + selected + 5 dependency types; only sorry warnings)`
- `lake env lean /tmp/dph_sh_ae_split/lean/ChildA.lean, ChildB.lean, Iface.lean, Final.lean (no errors or warnings; #print axioms: propext, Classical.choice, Quot.sound)`
- `python3 -I validate_lean_statement (verifier/lean_contract.py and /runtime/flows/gmt-claude-eb5f84b9e61e/_recursive_lean/lean_contract.py) on both child statements: unchanged, single line`
- `name collisions: python3 over dag.json lean_names (685 nodes; dph_sh_* = 6 names, none dph_sh_ae_*); rg -c 'dph_sh_ae_|affine_homotopy_contDiff_fderiv|affine_homotopy_isCompact_preimage_cyl' in the snapshot project and mathlib (exit 1, no match); grep GMT/ and .lake/packages/simongmt/Poincare (no match); git grep over the 1749 distinct ref-tip commits of 4096 refs -- '*.lean' (no match)`
- `read /runtime/flows/gmt-claude-eb5f84b9e61e/_recursive_lean/runtime.py (_existing_lean_name_problem, _solve_children, _overlay_accepted_children with prerequisite_ids = children + depends_on, _wait_for_accepted_dependencies, _implementation_plan) and speculation.py contract (children + depends_on)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Interval/Set/UnorderedInterval.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-h-88afce5b06/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-h-88afce5b06/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-homotopy-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-homotopy-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-h-f068722a83/decomposition-review-retry.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-h-33fe8712de/decomposition-review-retry.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-eb5f84b9e61e/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-eb5f84b9e61e/_recursive_lean/speculation.py`
- `/runtime/flows/gmt-claude-eb5f84b9e61e/_recursive_lean/lean_contract.py`
- `/tmp/dph_sh_ae_split/lean/AllStmts.lean`
- `/tmp/dph_sh_ae_split/lean/ChildA.lean`
- `/tmp/dph_sh_ae_split/lean/ChildB.lean`
- `/tmp/dph_sh_ae_split/lean/Iface.lean`
- `/tmp/dph_sh_ae_split/lean/Final.lean`

The pinned project, SimonGMT and the snapshot Mathlib contain no lemma on the straight-line homotopy G(y) = F₀(tl y) + t(y)(F₁ − F₀)(tl y): neither its smoothness or slice derivative nor its properness on [0,1] × S. So the two new children are genuine obligations. The accepted iwl_cr_ci_cone_map (cone map h = y₀·π(y)) is the direct precedent for splitting off such a calculus fact, and the grandparent's proof (Parts 5.1, 6.11) needs the same smoothness and properness. Mathlib supplies every input, identically in the snapshot and in .lake: HasFDerivAt.comp/fun_add/fun_sub/fun_smul, ContDiff.differentiable, IsCompact.cthickening, mem_cthickening_of_dist_le, Fin.cons_self_tail and IsCompact.of_isClosed_subset. Both child statements pass both lexical validators and elaborate in the replayed comparator scope, and each was proved in Lean. An interface theorem proves the exact selected type from the two children plus the five existing dependencies, taken with their frozen types. All of these checks use only propext, Classical.choice and Quot.sound. The two dph_sh_ae_ names are unused in the DAG, the project, SimonGMT, the snapshot and every ref-tip commit.
