# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.interior_form-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.interior_form-a1.coord_covector-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1–2 of the supplied proof of cbr_ci_pw_interior_product_form. There ε = ι_z(dy), i.e. ε(u_1, …, u_d) = det[z | u_1 | ⋯ | u_d]. This is the covector Σ_j z_jε_j of the parent's step 11(b), with ε_j = (−1)^{j−1}dy¹∧⋯∧dy^{j−1}∧dy^{j+1}∧⋯∧dyⁿ; compare the forms ω_j in the proof of Simon Ch. 6, Theorem 2.34 (book/chapter-06.txt lines 594–595).

Notation: e_l := EuclideanSpace.single l 1, and z_r is the r-th coordinate of z. For u : Fin d → ℝ^{d+1}, Fin.cons z u : Fin (d+1) → ℝ^{d+1} is the tuple (z, u_0, …, u_{d−1}).

1. (Continuous determinant form.) Let b := (EuclideanSpace.basisFun (Fin (d+1)) ℝ).toBasis, so b_l = e_l, and let D := b.det, the alternating (d+1)-linear map ℝ^{d+1} → ℝ with D(b) = 1. For c : Fin (d+1) → ℝ^{d+1} we have D(c) = det(b.toMatrix c) (Module.Basis.det_apply). The (r, l) entry of b.toMatrix c is the r-th coordinate of c_l, so D(c) = det(Matrix.of fun r l => (c l) r). The map c ↦ det(Matrix.of fun r l => (c l) r) is continuous. Each entry c ↦ (c l) r is the coordinate projection EuclideanSpace.proj r composed with the evaluation c ↦ c l (continuous_apply), so the matrix-valued map is continuous (continuous_matrix), and det of a continuous matrix-valued map is continuous (Continuous.matrix_det). So D together with this continuity is a continuous alternating map δ ∈ Covector (Euclid (d+1)) (d+1) with δ(c) = det(Matrix.of fun r l => (c l) r) for all c.
2. (Definition of ε.) Put ε := δ.curryLeft z ∈ Covector (Euclid (d+1)) d (ContinuousAlternatingMap.curryLeft). By ContinuousAlternatingMap.curryLeft_apply_apply, ε(u) = δ(Fin.cons z u) = det M(u) for every u : Fin d → ℝ^{d+1}. Here M(u) := Matrix.of fun r c => (Fin.cons z u c)_r is the (d+1)×(d+1) matrix whose column 0 is z and whose column k.succ is u_k, so M(u)_{r,0} = z_r and M(u)_{r,k.succ} = (u_k)_r.
3. (Laplace expansion.) Fix i ∈ Fin (d+1) and let u := i.removeNth e, so u_k = e_{i.succAbove k} (definition of Fin.removeNth). Expanding along column 0 (Matrix.det_succ_column_zero) gives det M(u) = Σ_{r ∈ Fin (d+1)} (−1)^r · M(u)_{r,0} · det N_r = Σ_r (−1)^r z_r det N_r. Here N_r := M(u).submatrix r.succAbove Fin.succ is the d×d matrix with entries (N_r)_{a,k} = M(u)_{r.succAbove a, k.succ} = (e_{i.succAbove k})_{r.succAbove a}. By PiLp.single_apply this entry is 1 if r.succAbove a = i.succAbove k and 0 otherwise.
4. (The term r = i.) (N_i)_{a,k} = 1 iff i.succAbove a = i.succAbove k iff a = k, because i.succAbove is injective (Fin.succAbove_right_inj). So N_i = 1 (Matrix.one_apply) and det N_i = 1 (Matrix.det_one). The r = i term is therefore (−1)^i z_i.
5. (The terms r ≠ i.) Let r ≠ i. Since i ≠ r, there is a₀ ∈ Fin d with r.succAbove a₀ = i (Fin.exists_succAbove_eq). The entries of row a₀ of N_r are (e_{i.succAbove k})_i. Each is 0, because i.succAbove k ≠ i for every k (Fin.succAbove_ne). A square matrix with a zero row has determinant 0 (Matrix.det_eq_zero_of_row_eq_zero), so det N_r = 0 and the r-th term (−1)^r z_r · 0 vanishes.
6. (Conclusion.) By steps 3–5 and Finset.sum_eq_single i (every r ≠ i contributes 0, and i ∈ univ), ε(i.removeNth e) = det M(u) = (−1)^i z_i. Since i was arbitrary, ε has the required property. The case d = 0 is the same computation: M(u) is the 1×1 matrix (z_0), the sum has the single term r = 0 = i, and N_0 is the empty 0×0 matrix, which is 1 with determinant 1. So ε() = z_0 = (−1)^0 z_0. ∎

## Key steps

1. Upgrade the standard-basis determinant b.det, with b.det c = det(Matrix.of fun r l => c l r), to a continuous (d+1)-covector δ via continuous_matrix and Continuous.matrix_det.
2. Set ε := δ.curryLeft z, so ε(u) = det M(u), where column 0 of M(u) is z and column k+1 is u_k (curryLeft_apply_apply).
3. Laplace expansion along column 0 at u = i.removeNth e: det M(u) = Σ_r (−1)^r z_r det N_r, with (N_r)_{a,k} = [r.succAbove a = i.succAbove k].
4. N_i is the identity (succAbove is injective), so det N_i = 1. For r ≠ i, row a₀ with r.succAbove a₀ = i is zero, so det N_r = 0.
5. Finset.sum_eq_single i gives ε(i.removeNth e) = (−1)^i z_i.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (mode local-project, project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp .../local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (SAME_CONTRACT); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (SAME_SUBMISSION)`
- `rg -n "theorem det_succ_column_zero|theorem orderEmbOfFin_unique |lemma exists_succAbove_eq |lemma succAbove_left_injective|lemma range_succAbove |lemma strictMono_succAbove|theorem curryLeft_apply_apply|theorem det_eq_zero_of_row_eq_zero|theorem extDeriv_apply|theorem Continuous.matrix_det|theorem EuclideanSpace.norm_eq|theorem basisFun_apply|theorem sum_repr" .../local-references/123e8435b4a2469b/mathlib/Mathlib (all found: Data/Finset/Sort.lean:260, Data/Fin/SuccPred.lean:661/669/676, Order/Fin/Basic.lean:191, Topology/Instances/Matrix.lean:212, Analysis/Normed/Module/Alternating/Curry.lean:57, LinearAlgebra/Matrix/Determinant/Basic.lean:362/734, Analysis/InnerProductSpace/PiL2.lean:145/494/806, Analysis/Calculus/DifferentialForm/Basic.lean:198)`
- `grep -n 'def removeNth' lake-packages-25730c7c/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean (removeNth p f i = f (p.succAbove i), line 845)`
- `cat lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean (Covector = E [⋀^Fin n]→L[ℝ] ℝ, exteriorDerivative = extDeriv, exteriorDerivative_apply) and head -120 Chapter06/Mass.lean (covectorEuclideanNorm = √Σ_{I : Fin n → Fin P, StrictMono I} α(basisFun ∘ I)²)`
- `python3 -I scans of .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json: lean_statement regex 'removeNth|succAbove|extDeriv|exteriorDerivative \(fun', 'covectorEuclideanNorm' (short, current-free), 'Matrix\.det|curryLeft' -> accepted dgcr_bwd_extDeriv_smul_const (candidate 9dcae6bdd5), dgcr_bwd_coordinate_covector (dcc3f4b7fc), cmr_cc_det_covector_exists, regcomp_covector_sq_sum_basisFun, codim1_lur_no_covector_eq_det_cons; codim1_lur_det_laplace_first_column is rlcr-lean (not reusable); cmcdt_lp_covector_norm_bounds is decomposing (not reusable)`
- `git show 9dcae6bdd56dfe358491f8344e7a8610f929bf88 -- GMT/Ch07/Submission.lean (accepted proof of Submission.dgcr_bwd_extDeriv_smul_const); git show dcc3f4b7fc0f6beb359e7585fbca8b266cc0f38f -- GMT/Ch07/Submission.lean (continuous-determinant covector construction pattern)`
- `lake env lean /tmp/cbrpw-decomp-7f3a/T0.lean (child and parent types elaborate), T1.lean (child coord_covector proof), T2.lean (child covector_norm proof), T3.lean (parent assembly from sorried children), T5.lean (all real proofs plus assembly; #print axioms: propext, Classical.choice, Quot.sound)`
- `python3 -I /tmp/cbrpw-decomp-7f3a/scripts/check.py verifier/lean_contract.py dag.json (validate_lean_statement PASS x3; cbr_ci_pw_ipf_coord_covector fresh, cbr_ci_pw_ipf_covector_norm_eq fresh, dgcr_bwd_extDeriv_smul_const existing accepted identical)`
- `grep/sed of /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (_decompose, _solve_children, _install_parent_supplied_child_handoff, _accepted_checkpoint, _existing_lean_name_problem, accepted-child overlay), leaf_verification.py check_source_delta, prompts.py DECOMPOSE/DECOMPOSITION_AUDIT, store.py ensure; swarm-project.json (max_depth 6, max_children 12)`
- `grep -n -i constancy book/chapter-06.txt; sed -n 565,600p book/chapter-06.txt (Simon Ch. 6, 2.34: ω_j = (−1)^{j−1} a dx^1∧⋯∧dx^{j−1}∧dx^{j+1}∧⋯∧dx^n, dω_j = (D_j a) dx^1∧⋯∧dx^n, lines 594–595)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-59d5577759/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-59d5577759/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-59d5577759/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-951a399d2e/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Finset/Sort.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Fin/SuccPred.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Fin/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/Matrix.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/swarm-project.json`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/prompts.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/store.py`
- `/tmp/cbrpw-decomp-7f3a/T0.lean`
- `/tmp/cbrpw-decomp-7f3a/T1.lean`
- `/tmp/cbrpw-decomp-7f3a/T2.lean`
- `/tmp/cbrpw-decomp-7f3a/T3.lean`
- `/tmp/cbrpw-decomp-7f3a/T5.lean`
- `/tmp/cbrpw-decomp-7f3a/scripts/check.py`

The snapshot contract is byte-identical to the workspace Contract.lean and Submission.lean (project b4d606db, Mathlib 25730c7c). Every library lemma used in the child proofs exists in the pinned snapshot: det_succ_column_zero, det_eq_zero_of_row_eq_zero, Finset.orderEmbOfFin_unique, Fin.exists_succAbove_eq, Fin.succAbove_left_injective, Fin.strictMono_succAbove, Continuous.matrix_det, ContinuousAlternatingMap.curryLeft_apply_apply, EuclideanSpace.norm_eq, EuclideanSpace.basisFun_apply, OrthonormalBasis.sum_repr, extDeriv_apply (wrapped by SimonGMT exteriorDerivative_apply). The DAG already holds a comparator-accepted Submission.dgcr_bwd_extDeriv_smul_const whose frozen type is byte-identical to the third child, so it is reused. The two new names are fresh. All child types elaborate in the contract scope and pass validate_lean_statement. Complete trial proofs of both new children and of the parent assembly from the three children compile under default heartbeats using only the standard axioms. The printed source of the identity is Simon Ch. 6, 2.34 (chapter-06.txt lines 594–595).
