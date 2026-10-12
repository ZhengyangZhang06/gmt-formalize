# Parent-supplied natural-language proof

- Parent DAG node: `root.stationary_results-a1.sff_properties-a1`
- Child DAG node: `root.stationary_results-a1.sff_properties-a1.mean_curvature_chart_continuous-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof steps 4–5 (the first half of step 5: "h is continuous on V"). Notation: A(x) := Dψ(x) = fderiv ℝ ψ x; S_x := D²ψ(x) = fderiv ℝ (fderiv ℝ ψ) x; G(x) := A(x)* ∘L A(x) with A(x)* = ContinuousLinearMap.adjoint A(x); G(x)⁻¹ := Ring.inverse G(x); e_k := EuclideanSpace.single k 1; P_z := tangentProjection M z; normalPart M z w = w − P_z w.
1. (Chart formula for H.) For x ∈ V, A(x) is injective (chart field injective_fderiv), tangentSpace M (ψ x) = range A(x), and secondFundamentalForm M (ψ x) (A(x)a) (A(x)b) = normalPart M (ψ x) (S_x a b) for all a, b (hypotheses). The sibling mean_curvature_gram (Submission.mean_curvature_eq_normalPart_gram_trace n N M (ψ x) (A(x)) S_x) therefore gives, for every x ∈ V, meanCurvature M (ψ x) = h(x) := w(x) − P_{ψ(x)} w(x), where w(x) := Σ_k Σ_l ⟨e_k, G(x)⁻¹ e_l⟩ • S_x e_k e_l. As the two functions agree on V, it suffices to prove that h is continuous on V (ContinuousOn.congr).
2. (First and second derivatives.) V is open and ψ is C² on V. Hence x ↦ A(x) is continuous on V (ContDiffOn.continuousOn_fderiv_of_isOpen, 1 ≤ 2); x ↦ A(x) is C¹ on V (ContDiffOn.fderiv_of_isOpen, 1 + 1 ≤ 2), so its derivative x ↦ S_x is continuous on V (continuousOn_fderiv_of_isOpen applied to x ↦ A(x), 1 ≤ 1).
3. (Gram operator and its inverse.) The adjoint L ↦ L* is a linear isometry (ℝⁿ →L ℝᴺ) → (ℝᴺ →L ℝⁿ), hence continuous, and composition of continuous linear maps is jointly continuous (ContinuousOn.clm_comp); so x ↦ G(x) is continuous on V. For x ∈ V, A(x) is injective, so G(x) is a unit of ℝⁿ →L[ℝ] ℝⁿ by the sibling gram_unit (Submission.gram_operator_isUnit_of_injective). This ring is a complete normed ring, and Ring.inverse is continuous at each of its units (NormedRing.inverse_continuousAt applied to the unit, rewritten with IsUnit.unit_spec). Composing, x ↦ G(x)⁻¹ is continuous within V at every x ∈ V, i.e. continuous on V.
4. (The vector field w.) For fixed k, l ∈ Fin n, x ↦ ⟨e_k, G(x)⁻¹ e_l⟩ is continuous on V (a continuous operator-valued map applied to a fixed vector, then paired with a fixed vector), and x ↦ S_x e_k e_l is continuous on V (step 2, evaluated twice at fixed vectors). Scalar multiples and finite sums of continuous maps are continuous, so w is continuous on V.
5. (Tangent projection along the chart.) ψ is continuous on V and maps V into M (ψ(V) = W ∩ M). Since z ↦ P_z is continuous on M by hypothesis, x ↦ P_{ψ(x)} is continuous on V (ContinuousOn.comp with MapsTo ψ V M). [This is where (TH2) of the parent enters; the parent equivalently writes P_{ψ(x)} = Π(A(x)) with Π(A) = A(A*A)⁻¹A* continuous on injective A.]
6. (Conclusion.) x ↦ P_{ψ(x)} w(x) is continuous on V (continuous operator-valued map applied to a continuous vector-valued map, ContinuousOn.clm_apply), so h = w − (P ∘ ψ) w is continuous on V, and by step 1 so is x ↦ meanCurvature M (ψ x). ∎
Formalization note. No imports beyond GMT.Ch02.Submission are needed. Use continuousOn_finsetSum for the double sum, ContinuousOn.inner and ContinuousOn.fun_smul (the `fun x ↦ f x • g x` form) for the summands. When composing NormedRing.inverse_continuousAt with the continuity of G, give the inner function explicitly: ContinuousAt.comp_continuousWithinAt (f := fun x ↦ ContinuousLinearMap.adjoint (fderiv ℝ ψ x) ∘L fderiv ℝ ψ x). This argument compiled warning-free against the frozen contract with only `import GMT.Ch02.Submission` (axioms propext, Classical.choice, Quot.sound, given the siblings).

## Key steps

1. By mean_curvature_gram, H(ψ(x)) = w(x) − P_{ψ(x)} w(x) on V, with w(x) = Σ_{k,l} ⟨e_k, G(x)⁻¹e_l⟩ • D²ψ(x)[e_k, e_l].
2. ψ ∈ C² on the open V, so Dψ and D²ψ are continuous on V.
3. G = (Dψ)*Dψ is continuous and unit-valued (gram_unit), and Ring.inverse is continuous at units, so G⁻¹ is continuous on V; hence w is continuous.
4. P ∘ ψ is continuous on V because P is continuous on M and ψ(V) ⊆ M; so w − (P∘ψ)w = H∘ψ is continuous on V.

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
