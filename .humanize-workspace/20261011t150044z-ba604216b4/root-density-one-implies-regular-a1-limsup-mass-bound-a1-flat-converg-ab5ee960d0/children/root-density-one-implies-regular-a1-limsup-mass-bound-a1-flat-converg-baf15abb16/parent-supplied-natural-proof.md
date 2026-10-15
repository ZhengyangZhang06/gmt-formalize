# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.face_replacement-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.face_replacement-a1.plane_orientation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 6, proof of 5.1, (26)–(27), as used in step 3 of the parent proof: on a face of L_n the orientation of Q is ±e_ι because the approximate tangent space there is the face plane V_ι, approximate tangent spaces being determined by their defining limits ("the defining limits determine the measure Hⁿ⌞Q, hence Q"). Here that argument is carried out for an arbitrary set A contained in the translate x + V_ι. Let V := span{e_{ι(0)}, …, e_{ι(n−1)}}; since ι is injective the e_{ι(j)} are orthonormal, dim V = n, and V = {v ∈ ℝ^P : v_i = 0 for every i ∉ range ι}.

1. Blow-ups lie in V. For λ > 0 and a ∈ A, the vector blowUpMap x λ a = λ⁻¹(a − x) has i-th coordinate λ⁻¹(a_i − x_i) = 0 for every i ∉ range ι, by (i). Hence blowUpMap x λ '' A ⊆ V for every λ > 0.

2. Q ⊆ V. If n = 0, dim Q = 0 forces Q = {0} ⊆ V. Let n ≥ 1 and suppose, for contradiction, q ∈ Q with q ∉ V. V is closed, so ρ := dist(q, V)/2 > 0 and the closed ball B̄(q, ρ) does not meet V. Let f(w) := max(0, ρ − dist(w, q)). f is continuous, nonnegative, vanishes outside the compact ball B̄(q, ρ) (so f ∈ C_c(ℝ^P)), f(q) = ρ > 0, and f = 0 on V. By step 1, f vanishes on blowUpMap x λ '' A, so ∫_{blowUpMap x λ '' A} f dHⁿ = 0 for every λ > 0 (setIntegral_eq_zero_of_forall_eq_zero); by (ii) these integrals tend to ∫_Q f dHⁿ, hence ∫_Q f dHⁿ = 0. On the other hand, choose an orthonormal basis τ₀ of Q (n vectors) and let ψ : ℝⁿ → ℝ^P, ψ(w) := Σ_k w_k τ₀_k, a linear isometry with range Q. By Isometry.map_euclideanHausdorffMeasure and μHE[n] = volume on Euclid n (EuclideanSpace.euclideanHausdorffMeasure_eq_volume), Hⁿ⌞Q = ψ#(volume); ψ is a closed, hence measurable, embedding, so ∫_Q f dHⁿ = ∫_{ℝⁿ} f(ψ(w)) dw (MeasurableEmbedding.integral_map). The function f∘ψ is continuous and nonnegative, has compact support (ψ⁻¹(B̄(q, ρ)) is closed and bounded because ψ is an isometry), and is nonzero at w₀ with ψ(w₀) = q. Lebesgue measure is positive on nonempty open sets and finite on compact sets, so ∫ f∘ψ > 0 (Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero), a contradiction. Hence Q ⊆ V.

3. Q = V. By (ii), dim Q = n = dim V, and Q ⊆ V; so Q = V (Submodule.eq_of_le_of_finrank_eq).

4. The orientation. By (iii) there is an orthonormal τ : Fin n → ℝ^P with span τ = Q = V and either ξ(α) = α(τ) for all α or ξ(α) = −α(τ) for all α. Each τ_k ∈ V, so τ_k = Σ_j M_{jk} e_{ι(j)} with M_{jk} := ⟨τ_k, e_{ι(j)}⟩. Since τ and (e_{ι(j)})_j are orthonormal bases of V, M is an orthogonal n × n matrix (MᵀM = I), so det M ∈ {1, −1}. For every n-covector α, multilinearity and the alternating property give α(τ) = Σ_{σ ∈ S_n} (∏_k M_{σ(k)k}) α(e_{ι(σ(0))}, …, e_{ι(σ(n−1))}) = Σ_σ sgn(σ) (∏_k M_{σ(k)k}) α(e_{ι(0)}, …, e_{ι(n−1)}) = det(M)·α(e_{ι(0)}, …, e_{ι(n−1)}), the terms with non-injective index maps vanishing. (Equivalently: the restriction of α to V equals α(e_ι)·det_{e_ι} by AlternatingMap.eq_smul_basis_det, and det_{e_ι}(τ) = ±1 for an orthonormal τ by OrthonormalBasis.det_to_matrix_orthonormalBasis_real.) Hence ξ(α) = ε·α(e_{ι(0)}, …, e_{ι(n−1)}) for all α, where ε := det M or ε := −det M is in {1, −1} and does not depend on α. If ε = 1 the first alternative holds, if ε = −1 the second. ∎

## Key steps

1. Every blow-up λ⁻¹(A − x) lies in V = span{e_{ι(j)}} because A ⊆ x + V.
2. A C_c test function supported near q ∈ Q ∖ V has zero blow-up integrals but positive integral over Q (Hⁿ⌞Q is Lebesgue measure transported by a linear isometry), so Q ⊆ V.
3. Equal dimensions give Q = V.
4. An orthonormal frame τ of V equals e_ι·M with M orthogonal, so α(τ) = det(M)·α(e_ι) with det M = ±1, and ξ = ±e_ι.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (mode local-project, project b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib 25730c7c759d108ef87ab70af2342a196760f79d); git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD (25730c7c…, matches)`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `grep -n 'theorem' local-references/…/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (Isometry.map_euclideanHausdorffMeasure, Isometry.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume)`
- `grep -n 'def HasApproximateTangentSpaceAt|def blowUpMap|def CountablyRectifiable|theorem countablyRectifiable_range|theorem countablyRectifiable_iUnion|theorem CountablyRectifiable.mono' SimonGMT/Chapter03/Rectifiable.lean`
- `sed SimonGMT/Chapter06/{Forms,Currents,Mass}.lean: Covector, DifferentialForm, exteriorDerivative (= extDeriv), exteriorDerivative_apply, TestFormOn, GeometricCurrentOn.continuous', GeometricCurrentOn.boundary_apply, covectorEuclideanNorm, massAdmissibleOn, massOn, le_massOn`
- `grep -rn 'wedgeCovectors|coord|basis' SimonGMT/Chapter06 (wedgeCovectors exists only in FormsDuality.lean, outside the import closure of GMT.Ch07.Contract, whose accepted Submissions keep the contract imports)`
- `grep Mathlib for alternatization_apply_apply, ContinuousMultilinearMap.mkPiAlgebra, EuclideanSpace.proj, StrictMono.range_inj_of_wellFoundedLT, EuclideanSpace.basisFun_apply, PiLp.single_apply, ENNReal.finsetSum_iSup, ENNReal.iSup_add_iSup_le, sSup_image', Real.smoothTransition, Filter.EventuallyEq.fderiv_eq, extDeriv_apply, LinearMap.trace_eq_matrix_trace, EuclideanSpace.norm_eq (all present in the pinned snapshot)`
- `python3 -I scans of runs/20261011T150044Z-ba604216b4/dag.json (updated 2026-10-13T23:22:24Z): status/candidate_commit/lean_statement of cmcdtfr_skeleton_null, dor_imrep_massOn_eq_measure_and_support, cmc_imRep_locality_restrict_sub, dor_lmb_fcd_cube_poincare; freshness of all dor_lmb_fcd_fr_* names; replay of _existing_lean_name_problem on the final child list (passes)`
- `git for-each-ref + git grep 'dor_lmb_fcd_fr_' -- GMT/Ch07 over all 7862 refs (no match)`
- `git show 09516d6d883db6c4d6e24410e2a32da5a8ae36f4:GMT/Ch07/Submission.lean (accepted Lean proof of cmcdtfr_skeleton_null, the model for skeleton_cells step 0)`
- `sed /runtime/flows/gmt-claude-889d520655ee/_recursive_lean/runtime.py (_existing_lean_name_problem, _accepted_checkpoint, _decompose: reuse needs an accepted checkpoint; nodes at depth ≥ max_depth are not decomposed) and store.py (refresh)`
- `verifier/gmt-compare.py child_modules / contract_scope (generated the exact NodeChallenge files)`
- `lake env lean /tmp/fr-decomp/lean/AllChallenges.lean (12 child types, exit 0); lake env lean /tmp/fr-decomp/lean/Assembly.lean (#print axioms: propext, Classical.choice, Quot.sound); lake env lean /tmp/fr-decomp/cc/CC1.lean (complete proof of the coordinate_covectors type, standard axioms)`
- `sed -n 10,185p book/chapter-06.txt (Simon 6.1: 1.1, 1.2, 1.5, 1.7, 1.15)`
- `python3 -I parse of this node's decomposition-v1.json and parent-child-handoff.json, and of the parent node's decomposition-v1.json and decomposition-audit-v1.json (reuse pattern of imrep_mass and im_calculus)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Multilinear/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/WellFounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/BigOperators.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/CompleteLattice/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-ab5ee960d0/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-ab5ee960d0/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-cab3e79dc1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-cab3e79dc1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-1dd1ac6935/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/runtime/flows/gmt-claude-889d520655ee/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-889d520655ee/_recursive_lean/store.py`
- `/tmp/fr-decomp/lean/AllChallenges.lean`
- `/tmp/fr-decomp/lean/Assembly.lean`
- `/tmp/fr-decomp/cc/CC1.lean`

Snapshot revisions are project b4d606db and mathlib 25730c7c. The snapshot Ch07 Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. The snapshot and SimonGMT contain no lattice-face, deformation or polyhedral-chain results usable here. FormsDuality.wedgeCovectors exists but lies outside the contract import closure, so the coordinate covectors are a new child built from Mathlib's alternatization. Every Mathlib/SimonGMT lemma cited in the child proofs exists in the pinned snapshot. Reuse: dor_imrep_massOn_eq_measure_and_support and cmc_imRep_locality_restrict_sub are accepted, have candidate commits and have byte-identical frozen types; they are also resolved dependencies of this node. cmcdtfr_skeleton_null is not reused, as the correction requires; its accepted argument (commit 09516d6) is inlined as step 0 of skeleton_cells. The 10 new dor_lmb_fcd_fr_* names are fresh in the DAG and all git refs. Lean: all 12 child types elaborate as exact comparator challenges. The assembly from the 12 child types plus the frozen CP type proves the selected frozen type with axioms [propext, Classical.choice, Quot.sound]. The new coordinate_covectors type has a complete compiled proof.
