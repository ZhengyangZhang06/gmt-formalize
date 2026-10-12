# Parent-supplied natural-language proof

- Parent DAG node: `root.stationary_results-a1.sff_properties-a1`
- Child DAG node: `root.stationary_results-a1.sff_properties-a1.mean_curvature_gram-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 2, 4.27 (H(y) = Σ_i B_y(τ_i, τ_i)); parent proof step 4 ("Mean curvature in a chart"), stated at a single point: A plays the role of A(x) = Dψ(x), S of S_x = D²ψ(x), and the two hypotheses are (TH1) and the chart formula (*) at x.
Notation. T := tangentSpace M y; P := tangentProjection M y = T.starProjection; w^⊥ := normalPart M y w = w − P w; B := secondFundamentalForm M y; d := finrank T; τ_i := tangentFrame M y i for i ∈ Fin d, which by definition is the i-th vector of the orthonormal basis b := stdOrthonormalBasis ℝ T of T, viewed in ℝᴺ; meanCurvature M y = Σ_i B(τ_i, τ_i) by definition.
1. (G is invertible.) By the sibling gram_unit (Submission.gram_operator_isUnit_of_injective n N A hA), G is a unit of ℝⁿ →L[ℝ] ℝⁿ. Hence G * G⁻¹ = 1 (Ring.mul_inverse_cancel), and since the product is composition, G(G⁻¹ v) = v for every v ∈ ℝⁿ.
2. (Preimages of the frame.) For each i ∈ Fin d, τ_i ∈ T = range A, so we may choose a_i ∈ ℝⁿ with A a_i = τ_i.
3. (H through S.) By hypothesis, B(τ_i, τ_i) = B(A a_i, A a_i) = (S a_i a_i)^⊥. The map w ↦ w^⊥ equals the continuous linear map id − P (definitionally), hence commutes with finite sums: meanCurvature M y = Σ_i (S a_i a_i)^⊥ = (Σ_i S a_i a_i)^⊥. It therefore suffices to prove Σ_i S a_i a_i = Σ_k Σ_l ⟨e_k, G⁻¹ e_l⟩ • S e_k e_l.
4. (Coordinates of a_i.) For all i and k, using step 1 and the adjoint identity ⟨A* w, v⟩ = ⟨w, A v⟩ (ContinuousLinearMap.adjoint_inner_left): ⟨e_k, a_i⟩ = ⟨G(G⁻¹ e_k), a_i⟩ = ⟨A*(A G⁻¹ e_k), a_i⟩ = ⟨A G⁻¹ e_k, A a_i⟩ = ⟨u_k, τ_i⟩, where u_k := A G⁻¹ e_k.
5. (Parseval in T.) Each u_k lies in range A = T. Since (τ_i) = (b_i) is an orthonormal basis of T, Parseval's identity in T (OrthonormalBasis.sum_inner_mul_inner, applied to the elements u_k, u_l of T, with Submodule.coe_inner to read the inner products in ℝᴺ) gives Σ_i ⟨u_k, τ_i⟩⟨u_l, τ_i⟩ = ⟨u_k, u_l⟩. Moreover ⟨u_k, u_l⟩ = ⟨A G⁻¹ e_k, A G⁻¹ e_l⟩ = ⟨A*A G⁻¹ e_k, G⁻¹ e_l⟩ = ⟨G G⁻¹ e_k, G⁻¹ e_l⟩ = ⟨e_k, G⁻¹ e_l⟩. Together with step 4: g^{kl} := ⟨e_k, G⁻¹ e_l⟩ = Σ_i ⟨e_k, a_i⟩⟨e_l, a_i⟩ for all k, l ∈ Fin n.
6. (Bilinear expansion.) Every v ∈ ℝⁿ satisfies v = Σ_k ⟨e_k, v⟩ • e_k (expansion in the orthonormal basis EuclideanSpace.basisFun (Fin n) ℝ, whose k-th vector is EuclideanSpace.single k 1: OrthonormalBasis.sum_repr' and EuclideanSpace.basisFun_apply). By bilinearity of S, S a_i a_i = Σ_k Σ_l (⟨e_k, a_i⟩⟨e_l, a_i⟩) • S e_k e_l. Summing over i and exchanging the finite sums (Finset.sum_comm, Finset.sum_smul), Σ_i S a_i a_i = Σ_k Σ_l (Σ_i ⟨e_k, a_i⟩⟨e_l, a_i⟩) • S e_k e_l = Σ_k Σ_l g^{kl} • S e_k e_l by step 5.
7. By steps 3 and 6, meanCurvature M y = normalPart M y (Σ_k Σ_l ⟨e_k, G⁻¹ e_l⟩ • S e_k e_l). No symmetry of S and no case distinction on n are needed (for n = 0 both sides are 0). ∎
Remark. Step 5 is the parent's identity g^{kl} = Σ_i ⟨e_k, a_i⟩⟨e_l, a_i⟩ ("the vectors a_i form a basis of ℝⁿ that is orthonormal for ⟨G u, v⟩"), verified through Parseval in T so that the dimension count d = n is not needed.
Formalization note. No imports beyond GMT.Ch02.Submission are needed. Use `choose a ha` for step 2; `normalPart M y v = (ContinuousLinearMap.id ℝ (Rn N) - tangentProjection M y) v` holds by rfl and lets map_sum do step 3; for step 1 rewrite with mul_apply_eq_comp, Ring.mul_inverse_cancel and one_apply_eq_self; for step 6 simp with map_sum, map_smul, sum_apply, smul_apply, Finset.smul_sum, smul_smul. This argument (about 70 Lean lines) compiled warning-free against the frozen contract with only `import GMT.Ch02.Submission` (axioms propext, Classical.choice, Quot.sound, given gram_unit).

## Key steps

1. G = A*A is a unit (gram_unit), so G(G⁻¹v) = v.
2. Choose a_i with A a_i = τ_i; then H(y) = Σ_i (S a_i a_i)^⊥ = (Σ_i S a_i a_i)^⊥ by the hypothesis on B and linearity of w ↦ w^⊥.
3. ⟨e_k, a_i⟩ = ⟨A G⁻¹e_k, τ_i⟩, and Parseval in T gives Σ_i ⟨e_k,a_i⟩⟨e_l,a_i⟩ = ⟨A G⁻¹e_k, A G⁻¹e_l⟩ = ⟨e_k, G⁻¹e_l⟩.
4. Expanding a_i in the standard basis and using bilinearity of S gives Σ_i S a_i a_i = Σ_{k,l} ⟨e_k, G⁻¹e_l⟩ • S e_k e_l.

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
