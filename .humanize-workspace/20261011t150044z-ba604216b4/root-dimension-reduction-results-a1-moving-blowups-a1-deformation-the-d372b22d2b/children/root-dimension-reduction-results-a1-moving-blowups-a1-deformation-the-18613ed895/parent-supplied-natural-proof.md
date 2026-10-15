# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.covector_bounds-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.covector_bounds-a1.pullback_le-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 3–4 of the selected parent proof, specialized and completed. Those steps are the one-slot estimate T_j ≤ ‖A‖²·T_{j−1}, iterated over the k slots, followed by (L0) from step 2. Here the telescoping chain T_k ≤ ‖A‖²·T_{k−1} ≤ … ≤ ‖A‖^{2k}·T_0 is organized as an induction on the degree that peels off the first slot with curryLeft. Each induction step is one application of the parent's one-slot estimate. Uses the sibling sq_sum (Submission.regcomp_covector_sq_sum_orthonormalBasis), which is identity (L0).

Notation. ℝ^M = Euclid M = EuclideanSpace ℝ (Fin M). Slots of an m-covector are indexed by Fin m = {0, …, m−1}, so the statement's (w_1, …, w_k) is written (w_0, …, w_{k−1}) below. e = (e_a)_{a ∈ Fin N} := EuclideanSpace.basisFun (Fin N) ℝ is the standard orthonormal basis of ℝ^N, and e' = (e'_b)_{b ∈ Fin N'} := EuclideanSpace.basisFun (Fin N') ℝ is that of ℝ^{N'}.
- For an m-covector γ on ℝ^M, a family b : Fin M → ℝ^M and j : Fin m → Fin M, write b∘j := (b_{j(0)}, …, b_{j(m−1)}) (Lean: fun i => b (j i)) and S_b(γ) := Σ_{j : Fin m → Fin M} γ(b∘j)².
- |α| := covectorEuclideanNorm α.
- For x ∈ ℝ^M and an (m+1)-covector γ on ℝ^M, ι_xγ := γ.curryLeft x is the m-covector w ↦ γ(x, w_0, …, w_{m−1}) (ContinuousAlternatingMap.curryLeft_apply_apply: γ.curryLeft x w = γ (Matrix.vecCons x w)). The map γ.curryLeft : ℝ^M →L[ℝ] Covector (ℝ^M) m is continuous linear in x.
- For an m-covector γ on ℝ^{N'}, A^#γ := γ.compContinuousLinearMap A, so (A^#γ)(w) = γ(A∘w) = γ(Aw_0, …, Aw_{m−1}) (ContinuousAlternatingMap.compContinuousLinearMap_apply).

1. (Parseval for functionals.) Let M ∈ ℕ, let e^{(M)}_a := EuclideanSpace.basisFun (Fin M) ℝ a, and let μ : ℝ^M →L[ℝ] ℝ be continuous linear. Then Σ_{a ∈ Fin M} μ(e^{(M)}_a)² = ‖μ‖².
Proof. Let g := (InnerProductSpace.toDual ℝ ℝ^M).symm μ be the Riesz vector of μ. Then ⟨g, x⟩ = μ(x) for all x (InnerProductSpace.toDual_symm_apply). Also ‖g‖ = ‖μ‖, because toDual is a linear isometric equivalence (LinearIsometryEquiv.norm_map). Parseval for the orthonormal basis e^{(M)} (OrthonormalBasis.sum_inner_mul_inner g g) gives Σ_a ⟨g, e^{(M)}_a⟩·⟨e^{(M)}_a, g⟩ = ⟨g, g⟩ = ‖g‖² (real_inner_self_eq_norm_sq). Each factor equals μ(e^{(M)}_a) by real_inner_comm, so Σ_a μ(e^{(M)}_a)² = ‖g‖² = ‖μ‖². For M = N the basis e^{(N)} is e; for M = N' it is e'.

2. (One-slot estimate, parent step 3.) For every continuous linear functional μ : ℝ^{N'} →L[ℝ] ℝ,
Σ_{a ∈ Fin N} μ(Ae_a)² ≤ ‖A‖²·Σ_{b ∈ Fin N'} μ(e'_b)².
Proof. μ∘A := μ.comp A is a continuous linear functional on ℝ^N with (μ∘A)(e_a) = μ(Ae_a). By step 1 with M = N, the left side equals ‖μ∘A‖². By step 1 with M = N', the right side equals ‖A‖²·‖μ‖². Since 0 ≤ ‖μ∘A‖ ≤ ‖μ‖·‖A‖ (ContinuousLinearMap.opNorm_comp_le), squaring (pow_le_pow_left₀) gives ‖μ∘A‖² ≤ (‖μ‖·‖A‖)² = ‖A‖²·‖μ‖². This is the parent's computation: if μ = ⟨g, ·⟩, then μ∘A = ⟨A*g, ·⟩ and Σ_i ⟨g, Ae_i⟩² = |A*g|² ≤ ‖A‖²·|g|².

3. (First-slot reindexing.) For M, m ∈ ℕ and every F : (Fin (m+1) → Fin M) → ℝ,
Σ_{J : Fin (m+1) → Fin M} F(J) = Σ_{a ∈ Fin M} Σ_{j : Fin m → Fin M} F(Fin.cons a j).
This holds because (a, j) ↦ Fin.cons a j is a bijection Fin M × (Fin m → Fin M) ≃ (Fin (m+1) → Fin M) (Fin.consEquiv; Fintype.sum_equiv and Fintype.sum_prod_type). Moreover, for every (m+1)-covector γ on ℝ^M and every family b : Fin M → ℝ^M, γ(b∘Fin.cons a j) = (ι_{b_a}γ)(b∘j). Indeed b∘Fin.cons a j = Matrix.vecCons b_a (b∘j): both agree on slot 0 and on every slot i.succ (Fin.cases). Then apply curryLeft_apply_apply.

4. (Hilbert–Schmidt inequality, the parent's chain of one-slot estimates.) Claim H(m), for every m ∈ ℕ: every m-covector γ on ℝ^{N'} satisfies S_e(A^#γ) ≤ (‖A‖²)^m·S_{e'}(γ), that is,
Σ_{j : Fin m → Fin N} (A^#γ)(e∘j)² ≤ (‖A‖²)^m·Σ_{j : Fin m → Fin N'} γ(e'∘j)².
The proof is by induction on m, for all γ simultaneously.
(a) m = 0. Each of Fin 0 → Fin N and Fin 0 → Fin N' has exactly one element (Fintype.sum_unique). The two argument tuples A∘(e∘j) and e'∘j' are maps out of Fin 0, hence equal (Subsingleton.elim). So both sums consist of the same single term γ(∅)², and (‖A‖²)^0 = 1.
(b) Step m → m+1. Let γ be an (m+1)-covector on ℝ^{N'}.
- By step 3 with M = N and b = e, S_e(A^#γ) = Σ_{a ∈ Fin N} Σ_{j : Fin m → Fin N} (ι_{e_a}(A^#γ))(e∘j)².
- For every x ∈ ℝ^N, ι_x(A^#γ) = A^#(ι_{Ax}γ), since both send w to γ(Ax, Aw_0, …, Aw_{m−1}) (Mathlib ContinuousAlternatingMap.curryLeft_compContinuousLinearMap). Hence S_e(A^#γ) = Σ_a S_e(A^#(ι_{Ae_a}γ)).
- Apply H(m) to the m-covector ι_{Ae_a}γ for each a, then exchange the finite sums (Finset.mul_sum, Finset.sum_comm):
S_e(A^#γ) ≤ Σ_a (‖A‖²)^m·Σ_{j : Fin m → Fin N'} (ι_{Ae_a}γ)(e'∘j)² = (‖A‖²)^m·Σ_{j : Fin m → Fin N'} Σ_{a ∈ Fin N} μ_j(Ae_a)².
Here, for fixed j, μ_j := (ContinuousAlternatingMap.apply ℝ (Euclid N') ℝ (e'∘j)).comp γ.curryLeft : ℝ^{N'} →L[ℝ] ℝ is the continuous linear functional μ_j(u) = (ι_uγ)(e'∘j) = γ(u, e'_{j(0)}, …, e'_{j(m−1)}).
- By step 2, Σ_a μ_j(Ae_a)² ≤ ‖A‖²·Σ_{b ∈ Fin N'} μ_j(e'_b)² for every j. Multiply by (‖A‖²)^m ≥ 0 and sum over j (monotonicity of finite sums; gcongr).
- Exchange the sums again and use (‖A‖²)^m·‖A‖² = (‖A‖²)^{m+1} (pow_succ):
S_e(A^#γ) ≤ (‖A‖²)^{m+1}·Σ_{b ∈ Fin N'} Σ_{j : Fin m → Fin N'} (ι_{e'_b}γ)(e'∘j)².
- By step 3 with M = N' and b = e', the double sum equals Σ_b Σ_j γ(e'∘Fin.cons b j)² = S_{e'}(γ). This proves H(m+1).

5. (Factorial identity (L0).) Apply the sibling sq_sum (Submission.regcomp_covector_sq_sum_orthonormalBasis) twice:
- with (P, n, α, f) := (N, k, A^#β, EuclideanSpace.basisFun (Fin N) ℝ), giving S_e(A^#β) = k!·|A^#β|²;
- with (P, n, α, f) := (N', k, β, EuclideanSpace.basisFun (Fin N') ℝ), giving S_{e'}(β) = k!·|β|².

6. (Conclusion.) H(k) for γ := β and step 5 give k!·|A^#β|² ≤ (‖A‖²)^k·k!·|β|². Since k! > 0 (Nat.factorial_pos), |A^#β|² ≤ (‖A‖²)^k·|β|² = (‖A‖^k·|β|)² (pow_mul, mul_pow). Both |A^#β| and ‖A‖^k·|β| are ≥ 0 (covectorEuclideanNorm_nonneg, norm_nonneg). Therefore |A^#β| ≤ ‖A‖^k·|β| (pow_le_pow_iff_left₀ with exponent 2). That is, covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β. The argument is uniform. For k = 0, H(0) is an equality and the conclusion reads |A^#β| ≤ 1·|β|. For N = 0 or N' = 0 all sums are finite and the same steps apply. ∎

## Key steps

1. Parseval for functionals Σ_a μ(e_a)² = ‖μ‖² (Riesz vector, OrthonormalBasis.sum_inner_mul_inner); hence the one-slot estimate Σ_a μ(Ae_a)² ≤ ‖A‖²·Σ_b μ(e'_b)² from ‖μ∘A‖ ≤ ‖μ‖·‖A‖.
2. First-slot reindexing J = Fin.cons a j (Fin.consEquiv) with γ(b∘Fin.cons a j) = (ι_{b_a}γ)(b∘j), and ι_x(A^#γ) = A^#(ι_{Ax}γ) (curryLeft_compContinuousLinearMap).
3. Hilbert–Schmidt inequality S_e(A^#γ) ≤ (‖A‖²)^m·S_{e'}(γ) by induction on m: induction hypothesis for ι_{Ae_a}γ, then the one-slot estimate for μ_j(u) = (ι_uγ)(e'∘j).
4. sq_sum turns S_e(A^#β) and S_{e'}(β) into k!·|A^#β|² and k!·|β|²; cancel k! and take square roots of nonnegative numbers.

## Reference use

### local-project

Queries:
- `cat SNAPSHOT/manifest.json (project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); git rev-parse HEAD in the workspace (b4d606db…) and in SNAPSHOT/mathlib (25730c7c…); cmp SNAPSHOT/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical)`
- `rg -n "covectorEuclideanNorm|curryLeft|compContinuousLinearMap" SNAPSHOT/project/GMT -g '*.lean' (no match); rg -n "pullback_norm|curryLeft_norm|covector_pullback|interior.*norm_le" SNAPSHOT/project/GMT -g '*.lean' (no match)`
- `rg -n "theorem .*covectorEuclideanNorm|covectorEuclideanNorm_" lake-packages-25730c7c/simongmt/Poincare -g '*.lean' (only covectorEuclideanNorm_zero, _nonneg, _neg in Chapter06/Mass.lean; definition of covectorEuclideanNorm in Mass.lean, Covector in Forms.lean)`
- `rg -n "curryLeft_apply_apply|curryLeft_compContinuousLinearMap|def curryLeft|compContinuousLinearMap_apply|^def apply|map_eq_zero_of_eq|sum_inner_mul_inner|Orthonormal.exists_orthonormalBasis_extension_of_card_eq|toDual_symm_apply|^def consEquiv|opNorm_comp_le|theorem map_perm" in SNAPSHOT/mathlib/Mathlib (all found)`
- `rg -n "curryLeft.*norm_le|norm_curryLeft|norm_compContinuousLinearMap_le" SNAPSHOT/mathlib/Mathlib/Analysis/Normed/Module/Alternating/ (norm_curryLeft, norm_compContinuousLinearMap_le exist but concern the operator/comass norm, not covectorEuclideanNorm)`
- `python3 scans of RUN/dag.json lean_statements for covectorEuclideanNorm/curryLeft/compContinuousLinearMap and lean_name lookups (accepted regcomp_covector_sq_sum_orthonormalBasis with identical type and candidate 16144a475b; unaccepted same-type copies cmcdt_lp_covector_pullback_norm_le, dimred_mbl_pf_oc_covectorEuclideanNorm_comp_le, cmcdt_lp_covector_curryLeft_norm_le; new names absent)`
- `git show 16144a475b272196ba8b2bd15f104028282dbcfc:GMT/Ch07/Submission.lean (accepted Lean code of regcomp_covector_sq_sum_basis_invariant, _basisFun, _orthonormalBasis); cat RUN/nodes/root-regular-components-are-minimizing-a1-imrep-mass-formula-a1-covec-c35871b74d/{parent-child-handoff.json,accepted-candidate.json,isolated-comparator-result.json,comparator-v1.log} (comparator passed)`
- `python3 read of the twin node RUN/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-884edba750/decomposition-v1.json and decomposition-audit-v1.json`
- `grep of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_decompose max_depth, _existing_lean_name_problem, _accepted_checkpoint, _solve_children, _install_parent_supplied_child_handoff) and store.py ensure; python3 -I /tmp/dmlp-cb-decomp/scripts/check_names.py (both validate_lean_statement implementations accept all three types)`
- `lake env lean /tmp/dmlp-cb-decomp/lean/Probe.lean, Pullback.lean, Curry.lean, Final.lean (#print axioms: propext, Classical.choice, Quot.sound), Assembly.lean, Challenge_sq_sum.lean, Challenge_pullback_le.lean, Challenge_curry_le.lean (only sorry warnings); python3 -I /tmp/dmlp-cb-decomp/scripts/numeric_pure.py (0 violations)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Dual.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-d372b22d2b/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-imrep-mass-formula-a1-covec-c35871b74d/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-imrep-mass-formula-a1-covec-c35871b74d/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-imrep-mass-formula-a1-covec-c35871b74d/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-imrep-mass-formula-a1-covec-c35871b74d/comparator-v1.log`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-884edba750/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-884edba750/decomposition-audit-v1.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/store.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/prompts.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/dmlp-cb-decomp/lean/Final.lean`
- `/tmp/dmlp-cb-decomp/lean/Assembly.lean`
- `/tmp/dmlp-cb-decomp/lean/Challenge_sq_sum.lean`
- `/tmp/dmlp-cb-decomp/lean/Challenge_pullback_le.lean`
- `/tmp/dmlp-cb-decomp/lean/Challenge_curry_le.lean`
- `/tmp/dmlp-cb-decomp/scripts/check_names.py`
- `/tmp/dmlp-cb-decomp/scripts/numeric_pure.py`

Pins match: project b4d606db and Mathlib 25730c7c. The workspace Submission is byte-identical to the snapshot's frozen Ch07 contract. Neither the snapshot project nor SimonGMT nor Mathlib has a bound on the Euclidean coefficient norm covectorEuclideanNorm under pull-back or interior product. SimonGMT only has covectorEuclideanNorm_zero, _nonneg and _neg. Mathlib's norm_curryLeft and norm_compContinuousLinearMap_le concern the operator/comass norm, which differs from covectorEuclideanNorm. So (L1) and (L2) are new obligations under fresh names (dimred_mbl_dt_lp_cb_pullback_le, dimred_mbl_dt_lp_cb_curryLeft_le). The unaccepted same-type DAG copies cannot be reused under the runtime rule. Identity (L0) already exists as the accepted regcomp_covector_sq_sum_orthonormalBasis with exactly the required type (candidate 16144a475b, comparator passed) and is reused verbatim. Every cited Mathlib name exists in the pinned snapshot. All three child types elaborate in the comparator's contract-mode challenge form and pass both validators. A Lean file containing the accepted sq_sum code and complete proofs of both new children derives the exact selected type, using only propext, Classical.choice and Quot.sound.
