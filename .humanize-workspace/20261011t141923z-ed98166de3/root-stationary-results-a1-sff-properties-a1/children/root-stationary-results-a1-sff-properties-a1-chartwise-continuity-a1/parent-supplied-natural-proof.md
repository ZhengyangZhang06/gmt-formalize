# Parent-supplied natural-language proof

- Parent DAG node: `root.stationary_results-a1.sff_properties-a1`
- Child DAG node: `root.stationary_results-a1.sff_properties-a1.chartwise_continuity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 5, second half ("ψ restricts to a homeomorphism of V onto W ∩ M; hence H = h ∘ (ψ|_V)⁻¹ is continuous on W ∩ M. Given y₀ ∈ M, choose such a chart with y₀ ∈ W; ... W is a neighbourhood of y₀, so H is continuous within M at y₀"), stated for an arbitrary F. The homeomorphism property comes from the relative properness of the chart. SimonGMT proves it as IsSimonLocalRepresentation.isEmbedding_chartMap / exists_open_image_eq_inter (Simon 4.2), but their module Poincare.SimonGMT.Chapter02.SubmanifoldTopology is not in the frozen import closure and a leaf may not add imports, so the needed instance of that argument is carried out directly from the chart fields.
1. Fix y₀ ∈ M. We show that F is continuous within M at y₀: for every neighbourhood O of F(y₀) in X, F⁻¹(O) is a neighbourhood of y₀ within M.
2. (A chart through y₀.) By the definition of IsSimonSubmanifold r M there is a chart (V, W, ψ) of class r with y₀ ∈ W. Since ψ(V) = W ∩ M ∋ y₀, there is x₀ ∈ V with ψ(x₀) = y₀.
3. (Continuity in the chart.) By hypothesis x ↦ F(ψ(x)) is continuous on V; as V is open and x₀ ∈ V, it is continuous at x₀ (ContinuousWithinAt.continuousAt). Hence there is an open U₀ ⊆ ℝⁿ with x₀ ∈ U₀ and F(ψ(x)) ∈ O for all x ∈ U₀.
4. (A compact piece of the chart.) W is open and y₀ ∈ W, so there is ε > 0 with Q := closedBall(y₀, ε) ⊆ W. Q is compact, so by the relative properness of the chart (isCompact_source_inter_preimage) K := V ∩ ψ⁻¹(Q) is compact. Then K \ U₀ = K ∩ U₀ᶜ is compact (a closed subset of a compact set, as U₀ is open), and ψ is continuous on V ⊇ K \ U₀ (ψ is C^r on V), so C := ψ(K \ U₀) is compact, hence closed in ℝᴺ.
5. (y₀ ∉ C.) If y₀ = ψ(x) with x ∈ K \ U₀ ⊆ V, then ψ(x) = ψ(x₀) with x, x₀ ∈ V, so x = x₀ by injectivity of ψ on V; but x₀ ∈ U₀ while x ∉ U₀, a contradiction.
6. (F maps a neighbourhood of y₀ in M into O.) W₀ := ball(y₀, ε) \ C is open (an open set minus a closed set) and contains y₀ (steps 4–5). Let z ∈ W₀ ∩ M. Then z ∈ ball(y₀, ε) ⊆ Q ⊆ W, so z ∈ W ∩ M = ψ(V): z = ψ(x) with x ∈ V, and x ∈ K because ψ(x) = z ∈ Q. If x ∉ U₀, then x ∈ K \ U₀ and z = ψ(x) ∈ C, contradicting z ∈ W₀; hence x ∈ U₀ and F(z) = F(ψ(x)) ∈ O by step 3. Thus W₀ ∩ M ⊆ F⁻¹(O).
7. Since W₀ is open and y₀ ∈ W₀, the set W₀ ∩ M, and hence F⁻¹(O) ⊇ W₀ ∩ M, is a neighbourhood of y₀ within M (mem_nhdsWithin). As O and y₀ ∈ M were arbitrary, F is continuous on M. ∎
Formalization note. Only the frozen imports are needed: the chart fields are exposed by Poincare.SimonGMT.Chapter02.Submanifold (image_eq, isOpen_source, isOpen_target, contDiffOn, injOn, isCompact_source_inter_preimage). Under the contract's `open Metric`, write `_root_.mem_nhds_iff` (Metric.mem_nhds_iff is also in scope). Useful names: nhds_basis_closedBall.mem_iff, isCompact_closedBall, IsCompact.diff, IsCompact.image_of_continuousOn, IsCompact.isClosed, isOpen_ball.sdiff, ball_subset_closedBall, mem_nhdsWithin. A Lean proof following steps 1–7 (about 35 lines) compiled warning-free against the frozen contract with only `import GMT.Ch02.Submission` and axioms propext, Classical.choice, Quot.sound.

## Key steps

1. Fix y₀ ∈ M and a class-r chart (V, W, ψ) with y₀ = ψ(x₀); continuity of F∘ψ at x₀ gives an open U₀ ∋ x₀ with F(ψ(U₀)) ⊆ O.
2. With Q = closedBall(y₀, ε) ⊆ W, relative properness makes K = V ∩ ψ⁻¹(Q) compact, so C = ψ(K \ U₀) is compact and closed.
3. Injectivity of ψ on V gives y₀ ∉ C, so W₀ = ball(y₀, ε) \ C is an open neighbourhood of y₀.
4. Every z ∈ W₀ ∩ M is ψ(x) with x ∈ K ∩ U₀, so F(z) ∈ O; hence F⁻¹(O) ∈ 𝓝[M] y₀ and F is continuous on M.

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
