# Parent-supplied natural-language proof

- Parent DAG node: `root.stationary_results-a1.sff_properties-a1`
- Child DAG node: `root.stationary_results-a1.sff_properties-a1.normal_field_identity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the identity "τ_i · D_{τ_j}X = −X · B(τ_i, τ_j) by virtue of 4.24 and the fact that X is normal to M" used in Simon's printed proof of 5.11; parent proof steps 0 and 3 (parent G3), with the parent's uses of (TH1) and of sff_chart replaced by the hypotheses (R) and (C).
Notation. ℝ^d := EuclideanSpace ℝ (Fin d) (= Rn d). For M ⊆ ℝᴺ and z ∈ ℝᴺ: T_z := tangentSpace M z (a submodule of ℝᴺ); P_z := tangentProjection M z = (tangentSpace M z).starProjection, the orthogonal projection of ℝᴺ onto T_z (a continuous linear map ℝᴺ → ℝᴺ); w^⊥ := normalPart M z w = w − P_z w; B_z(τ, η) := secondFundamentalForm M z τ η. A chart of class r of M is a triple (V, W, ψ), ψ : ℝⁿ → ℝᴺ, with Chapter02.IsSimonLocalRepresentation r M V W ψ: V ⊆ ℝⁿ open (isOpen_source), W ⊆ ℝᴺ open, ψ C^r on V (contDiffOn), ψ injective on V, ψ(V) = W ∩ M (image_eq), ψ relatively proper, and Dψ(x) := fderiv ℝ ψ x injective for every x ∈ V (injective_fderiv). D²ψ(x)[a, b] := fderiv ℝ (fderiv ℝ ψ) x a b (the derivative at x in direction a of x′ ↦ Dψ(x′)b).
1. (A chart through y.) As y ∈ M, there is a chart (V, W, ψ) of M of class 2 with y ∈ W, and, since ψ(V) = W ∩ M, some x ∈ V with ψ(x) = y. By (R), T_y = range Dψ(x), so τ = Dψ(x)a and η = Dψ(x)b for some a, b ∈ ℝⁿ. Put S(a′, b′) := D²ψ(x)[a′, b′].
2. (Regularity at x.) V is open, x ∈ V and ψ is C² on V. Hence ψ is differentiable at x with derivative Dψ(x), and x′ ↦ Dψ(x′) is C¹ on V (ContDiffOn.fderiv_of_isOpen with 1 + 1 ≤ 2), so it is differentiable at x with derivative fderiv ℝ (fderiv ℝ ψ) x. Consequently g(x′) := Dψ(x′)b has at x the derivative a′ ↦ D²ψ(x)[a′, b] = S(a′, b) (apply the operator-valued derivative to the constant vector b: HasFDerivAt.clm_apply with hasFDerivAt_const). Y is differentiable at ψ(x) = y, so by the chain rule Y ∘ ψ has at x the derivative DY(y) ∘ Dψ(x) (HasFDerivAt.comp).
3. (A function vanishing near x.) Let f(x′) := ⟨Y(ψ(x′)), Dψ(x′)b⟩. For every x′ ∈ V: ψ(x′) ∈ ψ(V) = W ∩ M ⊆ M, and Dψ(x′)b ∈ range Dψ(x′) = T_{ψ(x′)} by (R) at x′; since Y is normal along M, f(x′) = 0. As V is an open neighbourhood of x, f agrees with the zero function near x, so f has derivative 0 at x (HasFDerivAt.congr_of_eventuallyEq applied to the constant function 0).
4. (Product rule.) By the product rule for the inner product (HasFDerivAt.inner) and step 2, f has at x the derivative a′ ↦ ⟨Y(y), S(a′, b)⟩ + ⟨DY(y)(Dψ(x)a′), Dψ(x)b⟩. By uniqueness of Fréchet derivatives (HasFDerivAt.unique) and step 3, this linear map is 0; evaluating at a′ = a gives 0 = ⟨Y(y), S(a, b)⟩ + ⟨DY(y)τ, η⟩.
5. (Y(y) only sees the normal part.) Write S(a, b) = (S(a, b) − P_y S(a, b)) + P_y S(a, b) = S(a, b)^⊥ + P_y S(a, b). Since P_y S(a, b) ∈ T_y (Submodule.starProjection_apply_mem) and Y is normal along M at z = y ∈ M, ⟨Y(y), P_y S(a, b)⟩ = 0. Hence ⟨Y(y), S(a, b)⟩ = ⟨Y(y), S(a, b)^⊥⟩ = ⟨Y(y), B_y(τ, η)⟩, the last equality by (C) at x: B_y(Dψ(x)a, Dψ(x)b) = (D²ψ(x)[a, b])^⊥.
6. By steps 4 and 5 and the symmetry of the real inner product, ⟨η, DY(y)τ⟩ = ⟨DY(y)τ, η⟩ = −⟨Y(y), S(a, b)⟩ = −⟨Y(y), B_y(τ, η)⟩. ∎
Formalization note. No imports beyond GMT.Ch02.Submission are needed (HasFDerivAt.inner, HasFDerivAt.clm_apply are available). After evaluating the derivative identity at a, `simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, fderivInnerCLM_apply, Function.comp_apply, ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply, zero_apply]` normalises it to the scalar identity of step 4; then rewrite with (C), normalPart, inner_sub_right and real_inner_comm and finish by linarith. This argument compiled warning-free against the frozen contract with only `import GMT.Ch02.Submission` (axioms propext, Classical.choice, Quot.sound).

## Key steps

1. Take a class-2 chart with ψ(x) = y; by (R), τ = Dψ(x)a and η = Dψ(x)b.
2. f(x′) = ⟨Y(ψ(x′)), Dψ(x′)b⟩ vanishes on the open V by (R) and normality of Y, so Df(x) = 0.
3. Chain and product rules give 0 = Df(x)a = ⟨Y(y), D²ψ(x)[a,b]⟩ + ⟨DY(y)τ, η⟩.
4. ⟨Y(y), D²ψ(x)[a,b]⟩ = ⟨Y(y), (D²ψ(x)[a,b])^⊥⟩ = ⟨Y(y), B_y(τ,η)⟩ by normality of Y(y) and (C).

## Reference use

### local-project

Queries:
- `cat manifest.json; cmp project/GMT/Ch02/Contract.lean <workspace>/GMT/Ch02/Contract.lean; sed -n 83,176p Contract.lean (tangentSpace, tangentProjection, normalPart, tangentFrame, secondFundamentalForm, meanCurvature)`
- `cat SimonGMT Chapter02/{Submanifold,SubmanifoldTopology,SecondFundamentalForm,SecondFundamentalFormCalculus}.lean; grep -n '^theorem\|^def' SecondFundamentalForm*.lean SubmanifoldCalculus.lean SubmanifoldIntegral.lean`
- `grep -rn 'theorem ContDiffAt.isSymmSndFDerivAt\|theorem NormedRing.inverse_continuousAt\|theorem sum_inner_mul_inner\|theorem HasFDerivAt.inner\|def IsSymmSndFDerivAt\|theorem ContDiffOn.continuousOn_fderiv_of_isOpen\|theorem ContDiffOn.fderiv_of_isOpen' mathlib/Mathlib`
- `grep -rn 'inverse_continuousAt\|sub_starProjection_mem_orthogonal\|inner_left_of_mem_orthogonal\|ofInjectiveEndo\|def toUnit\|sum_repr\x27\|basisFun_apply\|inner_single_left\|Submodule.coe_inner\|adjoint_inner_left\|mul_apply_eq_comp\|ContinuousOn.fun_smul' mathlib/Mathlib`
- `Lean #eval of (← getEnv).header.moduleNames after `import GMT.Ch02.Submission`: membership of Mathlib.Analysis.Calculus.FDeriv.Symmetric, Poincare.SimonGMT.Chapter02.SubmanifoldTopology, Mathlib.Analysis.Calculus.MeanValue, Mathlib.Analysis.Normed.Ring.Units`
- `grep -rl <each proposed lean_name> over dag.json, nodes/, project snapshot, SimonGMT, Mathlib; git grep -l <name> $(git for-each-ref refs/heads refs/remotes) (positive control: c1_sard_coarea_jacobian_continuousOn)`
- `python3 gen.py: verifier gmt-compare.py contract_scope/child_modules + lean_contract.validate_lean_statement for the 7 lean_statements; lake build GMT.Ch02.Submission; lake env lean NodeChallenge_00..06.lean AssemblyCheck.lean FinalCheck.lean (#print axioms)`
- `python3 leafcheck.py: workflow _recursive_lean.leaf_verification.check_source_delta on each child theorem inserted into the frozen Submission.lean; ScopedDecomposition model validation of this payload`
- `read nodes/root-stationary-results-a1-sff-properties-a1/parent-child-handoff.json, nodes/root-stationary-results-a1-sff-chart-a1/parent-child-handoff.json, nodes/root-stationary-results-a1/decomposition-v1.json, dag.json; /runtime/flows/gmt-claude-6e6a457c9391/_recursive_lean/{runtime.py (_leaf_author_task), leaf_verification.py, parent_verification.py, prompts.py, models.py}`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Normed/Ring/Units.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Algebra/GroupWithZero/Units/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Orthogonal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Subspace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Algebra/Module/Equiv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Algebra/MulAction.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldTopology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SecondFundamentalForm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SecondFundamentalFormCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1-sff-properties-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1-sff-chart-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-6e6a457c9391/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-6e6a457c9391/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-6e6a457c9391/_recursive_lean/models.py`
- `/tmp/sffprop-decomp-2HH9Ps/FinalCheck.lean`
- `/tmp/sffprop-decomp-2HH9Ps/AssemblyCheck.lean`

The snapshot contract is byte-identical to the workspace contract. Contract.lean lines 83-125 fix the objects used:
- B = fderivWithin of tangentProjection;
- H = Σ over tangentFrame = stdOrthonormalBasis of T_y;
- normalPart = v − P v.
The snapshot project has no Submission.* declarations. None of the 7 proposed names occurs in dag.json, any node file, any git ref, the snapshot, SimonGMT or Mathlib.
Import closure of GMT.Ch02.Submission:
- Mathlib.Analysis.Calculus.FDeriv.Symmetric (ContDiffAt.isSymmSndFDerivAt, cited by the parent's step 1) is NOT in it.
- Poincare.SimonGMT.Chapter02.SubmanifoldTopology (isEmbedding_chartMap/exists_open_image_eq_inter, cited in step 5) is NOT in it.
- Leaves may insert exactly one theorem and change no imports (runtime._leaf_author_task, leaf_verification.check_source_delta).
- Hence Schwarz symmetry becomes its own child (mean-value proof), and chartwise continuity uses the relative-properness fields that Submanifold.lean exposes (isCompact_source_inter_preimage, injOn, image_eq).
Mathlib facts used, all in the closure: NormedRing.inverse_continuousAt, Ring.mul_inverse_cancel, OrthonormalBasis.sum_inner_mul_inner and sum_repr', EuclideanSpace.basisFun_apply, ContinuousLinearMap.adjoint_inner_left/right, Submodule.sub_starProjection_mem_orthogonal, starProjection_apply_mem, LinearEquiv.ofInjectiveEndo, ContinuousLinearEquiv.toUnit, HasFDerivAt.inner, ContDiffOn.fderiv_of_isOpen/continuousOn_fderiv_of_isOpen, norm_image_sub_le_of_norm_deriv_le_segment_01'.
SimonGMT's SecondFundamentalForm*.lean uses frame-based B (secondFundamentalFormFromNormalFrame), not the contract's fderivWithin form, so it is not reused.
Lean evidence:
- All 7 lean_statements pass validate_lean_statement and the workflow models; the generated NodeChallenge_00..06 compile.
- With only `import GMT.Ch02.Submission`, FinalCheck.lean proves all 7 children warning-free with axioms propext, Classical.choice, Quot.sound.
- The assembly proves the frozen selected type; its only extra axiom is sorryAx from the stubbed sibling sff_chart.
- Every child block passes check_source_delta.
- In Rn n →L[ℝ] Rn n, (G * H) v = G (H v) holds by rfl, so IsUnit/Ring.inverse are the composition inverse.
