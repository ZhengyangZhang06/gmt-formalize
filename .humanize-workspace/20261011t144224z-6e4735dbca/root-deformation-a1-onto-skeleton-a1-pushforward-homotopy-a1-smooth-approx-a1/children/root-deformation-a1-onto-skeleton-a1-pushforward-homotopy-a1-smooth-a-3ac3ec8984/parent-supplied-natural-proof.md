# Parent-supplied natural-language proof

- Parent DAG node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_approx-a1`
- Child DAG node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.smooth_approx-a1.covector_vanish-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step (4d) (alternating algebra) of the supplied proof of dph_lipschitz_smooth_approx, together with the observation of (4c) that DF_σ(x) maps ℝ^m into V_α = span{e_{α(q)}}, stated for an arbitrary continuous linear map T whose coordinates outside range α vanish (the parent applies it with γ = ω(G_j(x)) and T = fderiv ℝ G_j x).

Notation. e_i = EuclideanSpace.single i 1 (i ∈ Fin m′) is the standard basis of ℝ^{m′} = Eucl m′, and v_i (Lean: v i) is the i-th coordinate of v. α : Fin k → Fin m′ is strictly increasing, in particular injective. V := Fin k → ℝ (the real vector space ℝ^k) with standard basis b_q := Pi.single q 1 (q ∈ Fin k), i.e. b = Pi.basisFun ℝ (Fin k). For a k-linear map f and vectors u_0, …, u_{k−1}, f(u_0, …, u_{k−1}) is f applied to the family p ↦ u_p.

1. (The map S.) Define the linear map S : V → ℝ^{m′}, S(c) := Σ_{q∈Fin k} c_q e_{α(q)} (Fintype.linearCombination ℝ (q ↦ e_{α(q)})). For every q, S(b_q) = Σ_{q′} (b_q)_{q′} e_{α(q′)} = e_{α(q)}, since (b_q)_{q′} = 1 if q′ = q and 0 otherwise.

2. (T factors through S.) For v ∈ ℝ^m put π(v) := (q ↦ (Tv)_{α(q)}) ∈ V. Claim: Tv = S(π(v)). Compare i-th coordinates, i ∈ Fin m′: (e_{α(q)})_i = 1 if i = α(q) and 0 otherwise, so
   S(π v)_i = Σ_q (Tv)_{α(q)}·(e_{α(q)})_i = Σ_{q : α(q) = i} (Tv)_{α(q)}.
   - If i ∈ range α, say i = α(q₀), then q₀ is the only q with α(q) = i (α is injective), so S(π v)_i = (Tv)_{α(q₀)} = (Tv)_i.
   - If i ∉ range α, no q satisfies α(q) = i, so S(π v)_i = 0, and (Tv)_i = 0 by hypothesis.
   Thus all coordinates agree and Tv = S(π v).

3. (γ∘S vanishes.) γ′ := γ∘S, (c^0, …, c^{k−1}) ↦ γ(S c^0, …, S c^{k−1}), is an alternating k-linear map on the k-dimensional space V (in Lean γ.toAlternatingMap.compLinearMap S). For c^0, …, c^{k−1} ∈ V we have S c^p = Σ_q c^p_q e_{α(q)}, so by multilinearity
   γ′(c^0, …, c^{k−1}) = Σ_{τ : Fin k → Fin k} (Π_p c^p_{τ(p)}) · γ(e_{α(τ(0))}, …, e_{α(τ(k−1))}).
   If τ is not injective, say τ(p) = τ(p′) with p ≠ p′, then the arguments e_{α(τ(p))} and e_{α(τ(p′))} coincide and the term vanishes because γ is alternating (ContinuousAlternatingMap.map_eq_zero_of_not_injective). If τ is a permutation, γ(e_{α(τ(0))}, …, e_{α(τ(k−1))}) = sign(τ)·γ(e_{α(0)}, …, e_{α(k−1)}) (AlternatingMap.map_perm applied to γ.toAlternatingMap). Hence γ′(c^0, …, c^{k−1}) = det[c^p_q]·γ(e_{α(0)}, …, e_{α(k−1)}). This is exactly the identity γ′ = γ′(b_0, …, b_{k−1}) • det_b of AlternatingMap.eq_smul_basis_det for the basis b, because γ′(b_0, …, b_{k−1}) = γ(S b_0, …, S b_{k−1}) = γ(e_{α(0)}, …, e_{α(k−1)}) by step 1. By hypothesis γ(e_{α(0)}, …, e_{α(k−1)}) = 0, so γ′ = 0 • det_b = 0. (For k = 0 nothing changes: V is the zero space, every family is the empty family, and γ′(()) = γ(()) = γ(e_α) = 0.)

4. (Conclusion.) Let v_0, …, v_{k−1} ∈ ℝ^m. By step 2, Tv_p = S(π v_p) for every p, hence
   (γ.compContinuousLinearMap T)(v_0, …, v_{k−1}) = γ(Tv_0, …, Tv_{k−1}) = γ(S π v_0, …, S π v_{k−1}) = γ′(π v_0, …, π v_{k−1}) = 0
   by step 3. A continuous alternating map vanishing on every family is the zero map (extensionality), so γ.compContinuousLinearMap T = 0. ∎

## Key steps

1. S(c) := Σ_q c_q e_{α(q)} is linear on V = Fin k → ℝ with S(b_q) = e_{α(q)} for the standard basis b.
2. Tv = S(q ↦ (Tv)_{α(q)}): coordinates in range α agree by injectivity of α, the others vanish by hypothesis.
3. γ∘S is an alternating k-form on the k-dimensional V, so γ∘S = (γ∘S)(b)·det_b = γ(e_α)·det_b = 0 (multilinear expansion / AlternatingMap.eq_smul_basis_det).
4. γ(Tv_0, …, Tv_{k−1}) = (γ∘S)(πv_0, …, πv_{k−1}) = 0 for all families, so γ.compContinuousLinearMap T = 0 by extensionality.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `read nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-approx-a1/{parent-child-handoff.json,parent-supplied-natural-proof.json,parent-supplied-plan.md}: frozen type, supplied proof, depends_on = []; nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1/decomposition-v2.json (encoding of reused accepted children)`
- `python3 over dag.json (662 nodes): subtree of pushforward_homotopy-a1 (this node depth 4, status decomposing); regex 'molli|convol|mcshane|extend_real|bump|alternat|tangential|norm_fderiv|smooth_approx|smoothing' over lean_names/titles and 'McShane|Kirszbraun|extend_real|extend_pi|eq_smul_basis_det|alternating|convolution|lsmul' over statements; printed statements of slicing_mb_sa_mollifier_exists, slicing_mb_sa_mollify_lipschitz_close, slicing_mb_sa_mollify_lipschitz_hasFDerivAt, slicing_mb_smooth_approx, deformation_ipl_mwc_lipschitz_smooth_approx, slicing_im_ll_mollify, rpn_pe_convolution_contDiff_fderiv, smr_ci_covector_eq_zero_of_coord, cmb_covector_eq_sum_coord_smul_wedge, slicing_ru_covector_expansion, polyhedral_approx_pairing_covector_ext, ltg_covector_separating, lpf_rsn_covector_separating_family`
- `nodes/root-slicing-a1-slice-mass-bound-a1-smooth-approx-a1-mollifier-a1/{parent-child-handoff.json,isolated-comparator-result.json} (passed = true); git show 9735e2124d87ab3acc03bb8f199805df921599c5:GMT/Ch06/Submission.lean (accepted Lean proof of slicing_mb_sa_mollifier_exists); git show e9af228dd670dfa9a25505d00d9f3c1dab59b04d:GMT/Ch06/Submission.lean (this node's proof base: declaration absent)`
- `grep simongmt Chapter06/{Forms,Currents,FormsDuality}.lean: Covector E n = E [⋀^Fin n]→L[ℝ] ℝ, DifferentialForm E n = E → Covector E n, TestFormOn = testFormOnSubmodule, SimonMultiIndex n p = Fin n ↪o Fin p`
- `grep pinned Mathlib: LipschitzOnWith.extend_real (Topology/MetricSpace/Lipschitz.lean:308), LipschitzOnWith.extend_pi (:344), LipschitzOnWith.extend_finite_dimension (Analysis/Normed/Module/FiniteDimension.lean:207), HasCompactSupport.contDiff_convolution_left (Analysis/Calculus/ContDiff/Convolution.lean:427, order n : ℕ∞), convolution_lsmul (Analysis/Convolution.lean:423), norm_fderiv_le_of_lipschitzOn (Analysis/Calculus/FDeriv/Basic.lean:939), AlternatingMap.eq_smul_basis_det (LinearAlgebra/Determinant.lean:650), ContinuousAlternatingMap.compContinuousLinearMap and map_eq_zero_of_not_injective (Topology/Algebra/Module/Alternating/Basic.lean:314,137), ContinuousLinearMap.integral_comp_comm and integral_smul_const (MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean:70,219), Continuous.integrable_of_hasCompactSupport (MeasureTheory/Function/LocallyIntegrable.lean:622), norm_integral_le_of_norm_le (MeasureTheory/Integral/Bochner/Basic.lean:985), image_eq_one_of_notMem_mulTSupport (Topology/Algebra/Support.lean:111, additive form image_eq_zero_of_notMem_tsupport), Metric.mem_thickening_iff (Topology/MetricSpace/Thickening.lean:143), Metric.tendstoUniformly_iff (Topology/MetricSpace/Pseudo/Basic.lean:157), Filter.EventuallyEq.fderiv_eq (Analysis/Calculus/FDeriv/Congr.lean:260), EuclideanSpace.dist_eq/equiv/proj (Analysis/InnerProductSpace/PiL2.lean:158,276,285), PiLp.dist_apply_le (Analysis/Normed/Lp/PiLp.lean:652); no LipschitzOnWith.congr exists`
- `name uniqueness: python3 over dag.json lean_names; rg 'dph_sa_|mollify_lipschitz|covector_comp_eq_zero' over GMT/, .lake/packages/simongmt, .lake/packages/mathlib/Mathlib; git log --all -S 'dph_sa_' (no match anywhere)`
- `read /runtime/flows/*/_recursive_lean/runtime.py: _existing_lean_name_problem (accepted cross-branch reuse requires an identical lean_statement), child activation by lean_name, accepted reused children skip handoff installation`
- `python3 -I: verifier/lean_contract.py validate_lean_statement and verifier/gmt-compare.py contract_scope(GMT/Ch06/Contract.lean, GMT.Ch06.main_theorem) + child_modules on the 3 child statements and the parent statement`
- `lake env lean /tmp/dphsa/lean/{Stmts,Alt,Mol,Combined2}.lean and /tmp/dphsa-review/lean/IfaceNoExt.lean (parent from the two new child statements as hypotheses): statements elaborate; complete proofs of both new children; exact frozen parent proved from them; EXIT 0; axioms propext, Classical.choice, Quot.sound`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-approx-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-approx-a1/parent-supplied-natural-proof.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-smooth-approx-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-smooth-approx-a1-mollifier-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-smooth-approx-a1-mollifier-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/dphsa/lean/Combined2.lean`
- `/tmp/dphsa-review/lean/IfaceNoExt.lean`

Neither the pinned project nor SimonGMT has a vector-valued mollification with local Lipschitz, derivative and closeness bounds and locality of coordinates, or a lemma killing pulled-back covectors with image in span{e_α}. The DAG's accepted mollification lemmas are scalar-valued and/or global, and its accepted covector lemmas state different facts. So mollify (dph_sa_mollify_lipschitz) and covector_vanish (dph_sa_covector_comp_eq_zero) are new obligations, and both names are globally unique. The accepted slicing_mb_sa_mollifier_exists (candidate 9735e212, comparator passed) is exactly the mollifier of supplied step 2. It is reused by name with a byte-identical type, title and statement. This node's proof base e9af228d lacks it, so it must be a declared sibling. Mathlib's LipschitzOnWith.extend_finite_dimension covers supplied step 1, so there is no extension child. Every Mathlib lemma cited in the child proofs exists at the pinned commit. In Lean, both new children are fully proved, and the exact frozen parent is proved from them, with standard axioms only.
