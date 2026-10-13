# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.level_set_charts-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_triple-a1.level_set_charts-a1.tangent_range-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 7 of the parent proof (slicing_im_st_level_set_charts) together with the injectivity claim at the end of its Step 3 ("Dψ(v) is injective with |Dψ(v)u| ≥ |u|, because |Dψ(v)u| = lim_{s→0} |ψ(v + su) − ψ(v)|/|s|"), stated for a map ψ that is c-antilipschitz on an open set V on which h∘ψ is constant. In the parent it is applied with V := B(0, r), c := 1 and ψ the graph parametrization of the sibling local_graph.

Conventions. ℝ^k = Eucl k = EuclideanSpace ℝ (Fin k) with inner product ⟨·,·⟩ (inner ℝ) and Euclidean norm |·|; B(x, r) = ball x r is the open ball; Df(x) := fderiv ℝ f x for a map f.

1. (Dψ(v) is injective.) By the sibling fderiv_lower_bound (lpf_wtc_cat_fderiv_lower_bound applied with Q := m + 1, n := m, Φ := ψ, Ω := V, the constant c and w := v; its hypotheses hold because V is open, v ∈ V, ψ is differentiable at v and c|v′ − v″| ≤ |ψ(v′) − ψ(v″)| for all v′, v″ ∈ V), we have c|u| ≤ |Dψ(v)u| for every u ∈ ℝ^m. If Dψ(v)a = Dψ(v)b, then by linearity c|a − b| ≤ |Dψ(v)(a − b)| = |Dψ(v)a − Dψ(v)b| = 0; since c > 0 and |a − b| ≥ 0 this forces |a − b| = 0, i.e. a = b. So Dψ(v) is injective.

2. (range Dψ(v) ⊆ ker Dh(ψ(v)).) V is open and contains v, so V is a neighbourhood of v, and h(ψ(v′)) = h(ψ(v)) for all v′ ∈ V. Hence h∘ψ coincides near v with the constant function h(ψ(v)), and therefore D(h∘ψ)(v) = 0 (Filter.EventuallyEq.fderiv_eq and fderiv_const_apply). Since h is differentiable at ψ(v) and ψ is differentiable at v, the chain rule (fderiv_comp) gives D(h∘ψ)(v) = Dh(ψ(v)) ∘ Dψ(v). Thus Dh(ψ(v))(Dψ(v)u) = 0 for every u ∈ ℝ^m, i.e. range Dψ(v) ⊆ ker Dh(ψ(v)).

3. (Both subspaces have dimension m.)
   - By step 1 and LinearMap.finrank_range_of_inj, dim range Dψ(v) = dim ℝ^m = m (finrank_euclideanSpace_fin).
   - Dh(ψ(v)) ≠ 0, so there is u₀ with Dh(ψ(v))u₀ ≠ 0 (otherwise Dh(ψ(v)) = 0 by extensionality). Every y ∈ ℝ equals Dh(ψ(v))((y / Dh(ψ(v))u₀)·u₀), so range Dh(ψ(v)) = ℝ, of dimension 1. By rank–nullity (LinearMap.finrank_range_add_finrank_ker), 1 + dim ker Dh(ψ(v)) = dim ℝ^{m+1} = m + 1, hence dim ker Dh(ψ(v)) = m.

4. (range Dψ(v) = ker Dh(ψ(v)).) By steps 2 and 3, range Dψ(v) is a subspace of the finite-dimensional space ker Dh(ψ(v)) of the same dimension, so the two are equal (Submodule.eq_of_le_of_finrank_eq).

5. (Chain rule for Φ∘ψ.) Φ is differentiable at ψ(v) and ψ at v, so D(Φ∘ψ)(v) = DΦ(ψ(v)) ∘ Dψ(v) (fderiv_comp). The range of a composite of linear maps is the image of the range of the inner map under the outer map (LinearMap.range_comp): range D(Φ∘ψ)(v) = DΦ(ψ(v))(range Dψ(v)). By step 4 this equals DΦ(ψ(v))(ker Dh(ψ(v))), i.e. LinearMap.range (fderiv ℝ (Φ ∘ ψ) v) = Submodule.map (fderiv ℝ Φ (ψ v)) (LinearMap.ker (fderiv ℝ h (ψ v))). For m = 0 both sides are {0} and the same argument applies verbatim. ∎

Lean remark. The following proof was verified (Lean v4.35.0-rc3, Mathlib 25730c7c) as the declaration `theorem Submission.slicing_im_st_lsc_tangent_range : (<frozen statement>) := by` placed after the `end` of the `noncomputable section` and before `main_theorem` inside `namespace GMT.Ch06` of GMT/Ch06/Submission.lean, after the reused accepted declaration Submission.lpf_wtc_cat_fderiv_lower_bound. It needs no import beyond the frozen ones. Axioms: propext, Classical.choice, Quot.sound. The comparator-style check `exact Submission.slicing_im_st_lsc_tangent_range` against the frozen type in the contract scope also passed.
  have hFLB := Submission.lpf_wtc_cat_fderiv_lower_bound
  intro P m ψ Φ h V c v hV hv hc hψd hΦd hhd hdh hanti hconst
  -- (1) `c ‖u‖ ≤ ‖Dψ(v) u‖`, hence `Dψ(v)` is injective.
  have hlow := hFLB (m + 1) m ψ V c v hV hv hψd hanti
  have hinj : Function.Injective (fderiv ℝ ψ v) := by
    intro a b hab
    have h1 := hlow (a - b)
    rw [map_sub, hab, sub_self, norm_zero] at h1
    have h2 : ‖a - b‖ ≤ 0 := by nlinarith [norm_nonneg (a - b)]
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h2)
  -- (2) `h ∘ ψ` is constant near `v`, so `Dh(ψ v) ∘ Dψ(v) = D(h ∘ ψ)(v) = 0`.
  have hev : (h ∘ ψ) =ᶠ[𝓝 v] fun _ => h (ψ v) := by
    filter_upwards [hV.mem_nhds hv] with v' hv' using hconst v' hv'
  have hzero : fderiv ℝ (h ∘ ψ) v = 0 := by
    rw [hev.fderiv_eq]
    exact fderiv_const_apply _
  have hcomp : fderiv ℝ (h ∘ ψ) v = (fderiv ℝ h (ψ v)).comp (fderiv ℝ ψ v) :=
    fderiv_comp v hhd hψd
  have hle : LinearMap.range (fderiv ℝ ψ v).toLinearMap ≤
      LinearMap.ker (fderiv ℝ h (ψ v)).toLinearMap := by
    rintro _ ⟨u, rfl⟩
    have h3 := congrArg (fun L : Eucl m →L[ℝ] ℝ => L u) (hcomp.symm.trans hzero)
    simpa using h3
  -- (3) Both subspaces have dimension `m`, so they are equal.
  have hrange1 : Module.finrank ℝ (LinearMap.range (fderiv ℝ ψ v).toLinearMap) = m := by
    rw [LinearMap.finrank_range_of_inj hinj, finrank_euclideanSpace_fin]
  have htop : LinearMap.range (fderiv ℝ h (ψ v)).toLinearMap = ⊤ := by
    obtain ⟨u, hu⟩ : ∃ u, fderiv ℝ h (ψ v) u ≠ 0 := by
      by_contra hcon
      apply hdh
      ext u
      by_contra hu
      exact hcon ⟨u, by simpa using hu⟩
    rw [eq_top_iff]
    rintro y -
    refine ⟨(y / fderiv ℝ h (ψ v) u) • u, ?_⟩
    simp [hu]
  have hker : Module.finrank ℝ (LinearMap.ker (fderiv ℝ h (ψ v)).toLinearMap) = m := by
    have hrn := LinearMap.finrank_range_add_finrank_ker (fderiv ℝ h (ψ v)).toLinearMap
    rw [htop, finrank_top, Module.finrank_self, finrank_euclideanSpace_fin] at hrn
    omega
  have heq : LinearMap.range (fderiv ℝ ψ v).toLinearMap =
      LinearMap.ker (fderiv ℝ h (ψ v)).toLinearMap :=
    Submodule.eq_of_le_of_finrank_eq hle (hrange1.trans hker.symm)
  -- (4) Chain rule: `range D(Φ ∘ ψ)(v) = DΦ(ψ v)(range Dψ(v))`.
  have hcomp2 : fderiv ℝ (Φ ∘ ψ) v = (fderiv ℝ Φ (ψ v)).comp (fderiv ℝ ψ v) :=
    fderiv_comp v hΦd hψd
  rw [hcomp2]
  show LinearMap.range ((fderiv ℝ Φ (ψ v)).toLinearMap.comp (fderiv ℝ ψ v).toLinearMap) = _
  rw [LinearMap.range_comp, heq]

## Key steps

1. fderiv_lower_bound: c|u| ≤ |Dψ(v)u| on ℝ^m, so Dψ(v) is injective (c > 0).
2. h∘ψ is constant on the open set V ∋ v, so Dh(ψ(v)) ∘ Dψ(v) = D(h∘ψ)(v) = 0: range Dψ(v) ⊆ ker Dh(ψ(v)).
3. dim range Dψ(v) = m (injective) and dim ker Dh(ψ(v)) = m (nonzero functional onto ℝ, rank–nullity); hence equality.
4. Chain rule and LinearMap.range_comp: range D(Φ∘ψ)(v) = DΦ(ψ(v))(range Dψ(v)) = DΦ(ψ(v))(ker Dh(ψ(v))).

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); cmp snapshot project/GMT/Ch06/Contract.lean with the workspace Contract.lean (identical) and Contract.lean with Submission.lean (identical)`
- `read nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-level-s-aee3915817/{parent-child-handoff.json,parent-supplied-plan.md,parent-supplied-natural-proof.json} (frozen type, Steps 0-9 of the supplied proof)`
- `python3 over dag.json: id/lean_name/status/lean_statement of all 476 nodes; grep -iE 'antilip|implicit|level|chart|graph|bump|c1_|immersion|orthonormal|isometry|kernel' over the name list; lean_statement scan for 'implicit', 'level set', 'LinearMap.ker'`
- `grep -c 'slicing_im_st_lsc_' (and each full new name) in dag.json DAG.md issue-workers.json dag.mmd; grep -rl 'slicing_im_st_lsc' nodes/ local-references/197bdd4b88278494/project lake-packages-25730c7c/simongmt/Poincare (no match)`
- `read decomposition-v1.json of root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1 (fiw_ims_frame_sign reuse convention) and of root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1-me-70f87b0655 (earlier reuse of lpf_wtc_cat_fderiv_lower_bound, resolved to the accepted node in dag.json)`
- `read parent-supplied-natural-proof.{md,json} of root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-837491fcd9 (accepted proof and key steps of lpf_wtc_cat_fderiv_lower_bound); git show 8cfbc487a3d10545b0ea005ad58122242bbcc072 -- GMT/Ch06/Submission.lean (placement of accepted Submission.* declarations)`
- `rg in the Mathlib snapshot: ContDiffAt.implicitFunction, implicitFunction_apply_self, eventually_apply_eq_iff_implicitFunction, contDiffAt_implicitFunction, ContDiffAt.eventually, ContDiffBump (one_of_mem_closedBall, zero_of_le_dist, contDiffAt), hasContDiffBump_of_innerProductSpace, ContDiffOn.exists_lipschitzOnWith, TopologicalSpace.isOpen_iUnion_countable, Set.Countable.exists_eq_range, ContinuousLinearMap.IsInvertible, InnerProductSpace.toDual_symm_apply, stdOrthonormalBasis, OrthonormalBasis.reindex, ContinuousLinearMap.codRestrict, LinearMap.range_eq_top_of_ne_zero, LinearMap.finrank_range_of_inj, LinearMap.finrank_range_add_finrank_ker, Submodule.eq_of_le_of_finrank_eq, norm_add_sq_real, ball_prod_same, fderiv_comp, LinearMap.range_comp, Filter.EventuallyEq.fderiv_eq, ContDiff.continuous_fderiv, le_of_sq_le_sq, sq_le_sq₀`
- `lake env lean Check.lean: #check of the above after `import GMT.Ch06.Submission` (all available except ContDiffAt.implicitFunction* and LinearMap.range_eq_top_of_ne_zero; the former needs `import Mathlib.Analysis.Calculus.ImplicitContDiff`, whose olean is in lake-packages-25730c7c)`
- `gmt-compare.py contract_scope/child_modules (child scope: namespace GMT.Ch06 + contract opens, noncomputable section/end) and frozen_inputs/candidate_inputs (only GMT/Ch06/Submission.lean is not byte-frozen; imports unrestricted); import lines of 398 branch heads (earlier accepted candidates added Poincare.* imports)`
- `python3 -I validate.py: lean_contract.validate_lean_statement on the parent and the 5 child statements (all returned unchanged)`
- `lake env lean Stmts.lean (all child types elaborate in the comparator child scope); Assembly.lean (frozen parent type from the local_graph and tangent_range types as hypotheses: axioms propext, Classical.choice, Quot.sound); KernelFrame.lean, C1Extension.lean, LocalGraph.lean (from kernel_frame and c1_extension), TangentRange.lean (from fderiv_lower_bound): each standard axioms only`
- `lean -R sim -o sim/out/GMT/Ch06/Submission.olean sim/GMT/Ch06/Submission.lean (frozen Submission + import Mathlib.Analysis.Calculus.ImplicitContDiff + the 6 Submission.* declarations); LEAN_PATH=sim/out:$LEAN_PATH lean sim/Solutions.lean (comparator-style `exact Submission.X` for all 6 frozen types, #print axioms: propext, Classical.choice, Quot.sound)`
- `independent reviewer subagent: rebuilt the simulation from the JSON Lean remarks, compared reuse fields byte-for-byte, hashed the 56 frozen GMT.Ch06 declarations with/without the extra import (identical), ran gmt-compare.py with a simulated DAG for local_graph and the parent ('Your solution is okay!'); verdict ACCEPT`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/DAG.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/issue-workers.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.mmd`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-level-s-aee3915817/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-level-s-aee3915817/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-level-s-aee3915817/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1-interio-e2ad70d40d/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1-me-70f87b0655/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-837491fcd9/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-837491fcd9/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ImplicitContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/BumpFunction/InnerProduct.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Invertible.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Dual/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/Dual.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/Module/Submodule/Range.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/Dimension/Finrank.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Set/Countable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/Order/Ring/Abs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/.lake/build/lib/lean/Mathlib/Analysis/Calculus/ImplicitContDiff.olean`
- `/tmp/lsc-split-7731/Stmts.lean`
- `/tmp/lsc-split-7731/Assembly.lean`
- `/tmp/lsc-split-7731/KernelFrame.lean`
- `/tmp/lsc-split-7731/C1Extension.lean`
- `/tmp/lsc-split-7731/LocalGraph.lean`
- `/tmp/lsc-split-7731/TangentRange.lean`
- `/tmp/lsc-split-7731/sim/GMT/Ch06/Submission.lean`
- `/tmp/lsc-split-7731/sim/Solutions.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 contract, and the workspace Submission is byte-identical to it. No SimonGMT or project declaration and no DAG node provides local graph charts of regular level sets, an adapted kernel frame, a C¹ germ extension or the tangent-range identity. The names slicing_im_st_lsc_* occur nowhere in dag.json, DAG.md, issue-workers.json, dag.mmd, nodes/ or the snapshot. The only reusable accepted declaration is lpf_wtc_cat_fderiv_lower_bound (accepted, commit 8cfbc487), reused with its byte-identical type and accepted proof, as already done in the measurable_chart_differential decomposition. Mathlib supplies everything else: the C¹ implicit function theorem (ContDiffAt.implicitFunction with implicitFunction_apply_self, eventually_apply_eq_iff_implicitFunction, contDiffAt_implicitFunction), ContDiffBump on inner product spaces, ContDiffAt.eventually, ContDiffOn.exists_lipschitzOnWith, isOpen_iUnion_countable, Riesz duality, stdOrthonormalBasis and the finrank API. ImplicitContDiff is not imported by the frozen Submission. The comparator lets Submission.lean add imports, so only local_graph needs the extra import line. All 5 child types validate and elaborate in the comparator scope. Every new child is fully proved in Lean from its sibling dependencies, and the frozen parent type is proved from local_graph and tangent_range. Everything was kernel-checked in a simulated Submission module with comparator-style checks and standard axioms only, and independently re-verified, including by full gmt-compare.py runs.
