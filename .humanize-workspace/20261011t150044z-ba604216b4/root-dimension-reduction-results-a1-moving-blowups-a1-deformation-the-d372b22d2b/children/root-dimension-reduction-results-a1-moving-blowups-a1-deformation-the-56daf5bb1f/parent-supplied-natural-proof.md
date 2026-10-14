# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.covector_bounds-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.lipschitz_pushforward-a1.covector_bounds-a1.curry_le-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the selected parent proof, specialized and completed. That step normalizes v, extends v/|v| to an orthonormal basis f, and compares the Hilbert–Schmidt sums of ι_{f_1}β and β by keeping only the tuples in which the index of f_1 occurs exactly once. Here the bookkeeping "position p at which that index occurs" is written with the position sums R_p below. Uses the sibling sq_sum (Submission.regcomp_covector_sq_sum_orthonormalBasis), which is identity (L0).

Notation. ℝ^N = Euclid N with standard orthonormal basis e = EuclideanSpace.basisFun (Fin N) ℝ. Slots of an m-covector are indexed by Fin m = {0, …, m−1}, so the statement's (w_1, …, w_k) is written (w_0, …, w_{k−1}) below.
- For a family b : Fin N → ℝ^N (such as e or an orthonormal basis f of ℝ^N indexed by Fin N) and J : Fin m → Fin N, b∘J := (b_{J(0)}, …, b_{J(m−1)}) (Lean: fun i => b (J i)).
- For an m-covector α on ℝ^N, |α| := covectorEuclideanNorm α = √(Σ_{I : Fin m → Fin N} [I strictly increasing]·α(e∘I)²).
- For x ∈ ℝ^N, ι_xβ := β.curryLeft x is the k-covector w ↦ β(x, w_0, …, w_{k−1}) (ContinuousAlternatingMap.curryLeft_apply_apply: β.curryLeft x w = β (Matrix.vecCons x w)). The map β.curryLeft : ℝ^N →L[ℝ] Covector (ℝ^N) k is linear in x.

1. (Homogeneity of the coefficient norm.) For c ∈ ℝ and a k-covector γ on ℝ^N, |c•γ| = |c|·|γ|.
Each coefficient satisfies (c•γ)(e∘I) = c·γ(e∘I), so (c•γ)(e∘I)² = c²·γ(e∘I)². Hence the radicand of |c•γ| equals c²·X, where X ≥ 0 is the radicand of |γ| (Finset.mul_sum, termwise on both branches of `if StrictMono I`). Therefore |c•γ| = √(c²·X) = √(c²)·√X = |c|·|γ| (Real.sqrt_mul with c² ≥ 0, Real.sqrt_sq_eq_abs).

2. (Case v = 0.) β.curryLeft 0 = 0 (map_zero), so |ι_0β| = 0 (covectorEuclideanNorm_zero) and ‖0‖·|β| = 0. From now on assume v ≠ 0. Then N ≥ 1: for N = 0, ℝ^0 is a subsingleton and v would be 0. Put i₀ := ⟨0, _⟩ ∈ Fin N.

3. (Rotating v to a basis vector.) ‖v‖ > 0. Put u := ‖v‖⁻¹•v. Then ‖u‖ = ‖v‖⁻¹·‖v‖ = 1 (norm_smul, norm_inv, norm_norm) and v = ‖v‖•u (smul_smul, mul_inv_cancel₀).
- Let s := {i₀} ⊆ Fin N. The family indexed by s with constant value u is orthonormal: its only member has norm 1, and s contains no two distinct indices.
- finrank ℝ ℝ^N = N = card(Fin N). So Orthonormal.exists_orthonormalBasis_extension_of_card_eq (with v := fun _ => u and s := {i₀}) gives an orthonormal basis f : OrthonormalBasis (Fin N) ℝ (Euclid N) with f(i₀) = u.
- β.curryLeft is linear, so ι_vβ = ι_{‖v‖•u}β = ‖v‖•ι_uβ (map_smul). By step 1 and ‖v‖ ≥ 0, |ι_vβ| = ‖v‖·|ι_uβ|.
Hence it suffices to prove |ι_uβ| ≤ |β|. Then |ι_vβ| = ‖v‖·|ι_uβ| ≤ ‖v‖·|β| (mul_le_mul_of_nonneg_left).

4. (Position sums.) For J : Fin (k+1) → Fin N put g(J) := β(f∘J)² ≥ 0. For p ∈ Fin (k+1) put R_p := Σ_{J : Fin (k+1) → Fin N} [J(p) = i₀]·g(J) (Lean: ∑ J, if J p = i₀ then g J else 0).

5. (R_0 = k!·|ι_uβ|².) The map (a, j) ↦ Fin.cons a j is a bijection Fin N × (Fin k → Fin N) → (Fin (k+1) → Fin N) (Fin.consEquiv). Under it J(0) = a (Fin.cons_zero), so
R_0 = Σ_{a ∈ Fin N} Σ_{j : Fin k → Fin N} [a = i₀]·g(Fin.cons a j) = Σ_{j : Fin k → Fin N} g(Fin.cons i₀ j) (Fintype.sum_eq_single i₀).
Now f∘Fin.cons i₀ j = Matrix.vecCons (f i₀) (f∘j) = Matrix.vecCons u (f∘j): check slot 0 and every slot i.succ (Fin.cases). So g(Fin.cons i₀ j) = β(Matrix.vecCons u (f∘j))² = (ι_uβ)(f∘j)² (curryLeft_apply_apply). Hence R_0 = Σ_{j : Fin k → Fin N} (ι_uβ)(f∘j)², and this equals k!·|ι_uβ|² by sq_sum applied to (P, n, α, f) := (N, k, ι_uβ, f).

6. (R_p = R_0 for every p ∈ Fin (k+1).) Let σ := Equiv.swap 0 p ∈ Perm(Fin (k+1)); it is the identity if p = 0. Then σ⁻¹ = σ (Equiv.symm_swap) and σ(p) = 0 (Equiv.swap_apply_right).
- J ↦ J∘σ is a bijection of Fin (k+1) → Fin N: it is σ.arrowCongr (Equiv.refl (Fin N)), whose value at J is J∘σ⁻¹ = J∘σ. Substituting (Equiv.sum_comp), R_p = Σ_J [(J∘σ)(p) = i₀]·g(J∘σ).
- (J∘σ)(p) = J(σ p) = J(0).
- f∘(J∘σ) = (f∘J)∘σ, so β(f∘(J∘σ)) = sign(σ)·β(f∘J) (AlternatingMap.map_perm on β.toAlternatingMap). Since sign(σ) = ±1 (Int.units_eq_one_or), g(J∘σ) = g(J).
Therefore R_p = Σ_J [J(0) = i₀]·g(J) = R_0. This is the parent's remark that moving f_{i₀} to the front only permutes the arguments, so β(f_{I'}) = ±β(f_{i₀}, f_I).

7. (Σ_p R_p ≤ Σ_J g(J).) Exchanging the finite sums (Finset.sum_comm), Σ_p R_p = Σ_J Σ_p [J(p) = i₀]·g(J). It suffices to show Σ_p [J(p) = i₀]·g(J) ≤ g(J) for every J.
- Case 1: there are positions p ≠ q with J(p) = J(q) = i₀. Then the tuple f∘J has the equal entries f_{i₀} in the distinct slots p and q. Since β is alternating, β(f∘J) = 0 (ContinuousAlternatingMap.map_eq_zero_of_eq). So g(J) = 0 and both sides are 0.
- Case 2: otherwise. The set {p : J(p) = i₀} has at most one element (Finset.card_le_one). So Σ_p [J(p) = i₀]·g(J) = #{p : J(p) = i₀}·g(J) ≤ 1·g(J) = g(J) (Finset.sum_ite, Finset.sum_const, g(J) ≥ 0).
This is the parent's restriction to the tuples in which i₀ occurs exactly once: tuples containing i₀ at least twice contribute 0, and the dropped terms are ≥ 0.

8. (Total sum.) Σ_{J : Fin (k+1) → Fin N} g(J) = (k+1)!·|β|², by sq_sum applied to (P, n, α, f) := (N, k+1, β, f).

9. (Conclusion.) By step 6, Σ_p R_p = (k+1)·R_0. Combine this with steps 5, 7 and 8 and with (k+1)! = (k+1)·k! (Nat.factorial_succ): (k+1)·k!·|ι_uβ|² ≤ (k+1)·k!·|β|². Since (k+1)·k! > 0, |ι_uβ|² ≤ |β|². Both norms are ≥ 0 (covectorEuclideanNorm_nonneg), so |ι_uβ| ≤ |β| (pow_le_pow_iff_left₀ with exponent 2). By step 3, |ι_vβ| = ‖v‖·|ι_uβ| ≤ ‖v‖·|β|, that is, covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β. The argument is uniform. k = 0 needs no separate case: Fin 0 → Fin N has one element and 0! = 1. Nor does k+1 > N: every J then repeats an index, so all g(J) and R_p vanish. ∎

## Key steps

1. Homogeneity |c•γ| = |c|·|γ| and the case v = 0; otherwise reduce to u = v/‖v‖ = f(i₀) for an orthonormal basis f (Orthonormal.exists_orthonormalBasis_extension_of_card_eq).
2. Position sums R_p := Σ_J [J(p) = i₀]·β(f∘J)²; R_0 = k!·|ι_uβ|² by Fin.cons reindexing and sq_sum.
3. R_p = R_0 for every p via the transposition swap 0 p (sign² = 1).
4. Σ_p R_p ≤ Σ_J β(f∘J)² = (k+1)!·|β|², because tuples containing i₀ twice vanish; hence |ι_uβ| ≤ |β| and |ι_vβ| ≤ ‖v‖·|β|.

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
