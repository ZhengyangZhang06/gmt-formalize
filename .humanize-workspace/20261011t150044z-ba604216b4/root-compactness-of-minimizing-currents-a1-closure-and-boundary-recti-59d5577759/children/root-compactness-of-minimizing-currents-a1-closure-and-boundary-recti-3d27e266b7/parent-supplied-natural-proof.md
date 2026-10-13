# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.interior_form-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.interior_form-a1.covector_norm-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3 of the supplied proof of cbr_ci_pw_interior_product_form. The coefficient norm of ε = Σ_j z_jε_j is |z| because 'the ε_j are orthonormal for the coefficient norm' (parent step 11(b)); Simon's coefficient norm is (6.1.15), Remark 6.2.6.

Notation: e_l := EuclideanSpace.single l 1, z_i is the i-th coordinate of z, and b := EuclideanSpace.basisFun (Fin (d+1)) ℝ, so b_l = e_l (EuclideanSpace.basisFun_apply).

1. (Unfolding the norms.) By definition covectorEuclideanNorm ε = √S, where S := Σ_{I : Fin d → Fin (d+1)} (if StrictMono I then ε(fun k => b_{I k})² else 0). By EuclideanSpace.norm_eq, ‖z‖ = √(Σ_{i ∈ Fin (d+1)} ‖z_i‖²) = √(Σ_i z_i²) (Real.norm_eq_abs, sq_abs). So it suffices to prove S = Σ_i z_i².
2. (Strictly increasing maps Fin d → Fin (d+1).) Claim: a map I : Fin d → Fin (d+1) is strictly monotone iff I = i.succAbove for some i ∈ Fin (d+1). If I = i.succAbove, then I is strictly monotone (Fin.strictMono_succAbove). Conversely, let I be strictly monotone. I is not surjective, since a surjection Fin d → Fin (d+1) would give d + 1 = card (Fin (d+1)) ≤ card (Fin d) = d (Fintype.card_le_of_surjective), which is false. So there is i ∈ Fin (d+1) with I k ≠ i for all k. Let s := Finset.univ.erase i ⊆ Fin (d+1), so card s = d. Both I and i.succAbove map into s: I k ≠ i by the choice of i, and i.succAbove k ≠ i by Fin.succAbove_ne. Both are strictly monotone. By uniqueness of the increasing enumeration of a finset (Finset.orderEmbOfFin_unique with card s = d), each equals s.orderEmbOfFin, so I = i.succAbove.
3. (Reindexing the sum.) By Finset.sum_filter, S = Σ_{I ∈ univ.filter StrictMono} ε(fun k => b_{I k})². By step 2, univ.filter StrictMono = univ.image (fun i : Fin (d+1) => i.succAbove) as finsets of maps Fin d → Fin (d+1), and i ↦ i.succAbove is injective (Fin.succAbove_left_injective). Hence by Finset.sum_image, S = Σ_{i ∈ Fin (d+1)} ε(fun k => b_{i.succAbove k})².
4. (Evaluating each term.) For each i, (fun k => b_{i.succAbove k}) = (fun k => e_{i.succAbove k}) = i.removeNth e, by the definition of Fin.removeNth and b_l = e_l. By hypothesis ε(i.removeNth e) = (−1)^i z_i, so ε(fun k => b_{i.succAbove k})² = ((−1)^i)² z_i² = z_i², since ((−1)^i)² = (−1)^{2i} = ((−1)²)^i = 1.
5. (Conclusion.) S = Σ_i z_i², so covectorEuclideanNorm ε = √S = √(Σ_i z_i²) = ‖z‖. For d = 0 the argument is the same: the only map Fin 0 → Fin 1 is strictly monotone and equals (0 : Fin 1).succAbove, and S = ε()² = z_0². ∎

## Key steps

1. Unfold covectorEuclideanNorm and EuclideanSpace.norm_eq; it suffices to show S := Σ_{I strictly increasing} ε(b∘I)² equals Σ_i z_i².
2. A strictly increasing I : Fin d → Fin (d+1) misses some i, and then I = i.succAbove (Finset.orderEmbOfFin_unique on univ.erase i). Conversely each i.succAbove is strictly increasing.
3. Reindex: univ.filter StrictMono = univ.image succAbove with succAbove injective, so S = Σ_i ε(b∘i.succAbove)².
4. b∘i.succAbove = i.removeNth e and ((−1)^i z_i)² = z_i², so S = Σ_i z_i² and covectorEuclideanNorm ε = ‖z‖.

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
