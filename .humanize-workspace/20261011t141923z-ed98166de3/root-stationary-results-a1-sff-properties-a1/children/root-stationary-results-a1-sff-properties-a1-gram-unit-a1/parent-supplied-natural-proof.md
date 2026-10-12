# Parent-supplied natural-language proof

- Parent DAG node: `root.stationary_results-a1.sff_properties-a1`
- Child DAG node: `root.stationary_results-a1.sff_properties-a1.gram_unit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 4 ("G(x) := A(x)*A(x) (symmetric, positive definite, invertible)") and step 5 ("inversion is continuous on invertible operators"); this child isolates the invertibility of the Gram operator, which both the chart formula for H (sibling mean_curvature_gram) and its continuity (sibling mean_curvature_chart_continuous) use.
Setting. A : ℝⁿ →L[ℝ] ℝᴺ is injective, A* := ContinuousLinearMap.adjoint A : ℝᴺ →L[ℝ] ℝⁿ is characterised by ⟨u, A* w⟩ = ⟨A u, w⟩ for u ∈ ℝⁿ, w ∈ ℝᴺ (ContinuousLinearMap.adjoint_inner_right), and G := A* ∘L A. In the monoid ℝⁿ →L[ℝ] ℝⁿ the product is composition, (S * T) v = S (T v), and 1 = id.
1. (Trivial kernel.) Let w ∈ ℝⁿ with G w = 0. Then ‖A w‖² = ⟨A w, A w⟩ = ⟨w, A*(A w)⟩ = ⟨w, G w⟩ = ⟨w, 0⟩ = 0, so A w = 0 = A 0 (inner_self_eq_zero), and injectivity of A gives w = 0.
2. (Injectivity.) If G u = G v, then G(u − v) = G u − G v = 0 by linearity, so u − v = 0 by step 1, i.e. u = v. Thus G is injective.
3. (Bijectivity.) ℝⁿ is finite-dimensional and G is an injective linear endomorphism of it, hence G is surjective (rank–nullity); Mathlib packages this as the linear automorphism LinearEquiv.ofInjectiveEndo G.toLinearMap (step 2), whose underlying function is G. A linear map between finite-dimensional normed spaces is continuous, so this automorphism and its inverse are continuous: it upgrades to a continuous linear automorphism e : ℝⁿ ≃L[ℝ] ℝⁿ (LinearEquiv.toContinuousLinearEquiv) with e v = G v for every v.
4. (Unit.) A continuous linear automorphism e of ℝⁿ gives the unit e.toUnit of ℝⁿ →L[ℝ] ℝⁿ (ContinuousLinearEquiv.toUnit), whose underlying continuous linear map is e (as a map). By step 3 this underlying map equals G (ext: both send v to G v). Hence IsUnit G, i.e. IsUnit (ContinuousLinearMap.adjoint A ∘L A). ∎
Formalization note. No imports beyond GMT.Ch02.Submission are needed. The multiplication on ℝⁿ →L[ℝ] ℝⁿ used by IsUnit is composition ((G * H) v = G (H v) holds by rfl), so the unit is the operator inverse, not a pointwise one. A 20-line Lean proof following steps 1–4 (ContinuousLinearMap.adjoint_inner_right, inner_self_eq_zero, LinearEquiv.ofInjectiveEndo, LinearEquiv.toContinuousLinearEquiv, ContinuousLinearEquiv.toUnit) compiled warning-free against the frozen contract with only `import GMT.Ch02.Submission` and axioms propext, Classical.choice, Quot.sound.

## Key steps

1. G w = 0 implies ‖A w‖² = ⟨w, A*A w⟩ = 0, so A w = 0 and w = 0; hence G is injective.
2. An injective endomorphism of the finite-dimensional ℝⁿ is a linear automorphism, automatically continuous (ofInjectiveEndo, toContinuousLinearEquiv).
3. The continuous linear automorphism yields a unit of ℝⁿ →L[ℝ] ℝⁿ (toUnit) whose value is G, so IsUnit (A* ∘L A).

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
