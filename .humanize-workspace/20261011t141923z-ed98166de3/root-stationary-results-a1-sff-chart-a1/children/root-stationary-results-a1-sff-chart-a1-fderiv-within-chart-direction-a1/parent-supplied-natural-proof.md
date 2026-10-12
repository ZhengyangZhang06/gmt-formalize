# Parent-supplied natural-language proof

- Parent DAG node: `root.stationary_results-a1.sff_chart-a1`
- Child DAG node: `root.stationary_results-a1.sff_chart-a1.fderiv_within_chart_direction-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 6–7 of the supplied proof of second_fundamental_form_chart_formula, i.e. the derivative of P within M and the fact that chart directions lie in the tangent cone. M need not have unique differentiability at ψ(x₀), so fderivWithin is only determined on the tangent cone; this lemma evaluates it on chart directions only.
Notation: y₀ := ψ(x₀), A₀ := Dψ(x₀) = fderiv ℝ ψ x₀, L₀ := Dg(y₀) = fderiv ℝ g y₀. Fix a ∈ ℝⁿ.
1. (y₀ ∈ M and f(y₀) = g(y₀).) V ∈ 𝓝 x₀ implies x₀ ∈ V (mem_of_mem_nhds), so y₀ = ψ(x₀) ∈ ψ(V) ⊆ M. An eventual equality in 𝓝[M] y₀ holds at y₀ when y₀ ∈ M (Filter.EventuallyEq.eq_of_nhdsWithin), so f(y₀) = g(y₀).
2. (L₀ is a derivative of f within M.) g has Fréchet derivative L₀ at y₀, hence also derivative L₀ within M at y₀ (HasFDerivAt.hasFDerivWithinAt). f = g on M near y₀ and f(y₀) = g(y₀) by step 1. So HasFDerivWithinAt f L₀ M y₀ (HasFDerivWithinAt.congr_of_eventuallyEq).
3. (fderivWithin is a derivative within M.) By step 2, f is differentiable within M at y₀. So HasFDerivWithinAt f (fderivWithin ℝ f M y₀) M y₀ (DifferentiableWithinAt.hasFDerivWithinAt). This holds in all cases, including when y₀ is isolated in M.
4. (Uniqueness on the tangent cone.) Two derivatives of f within M at y₀ agree on tangentConeAt ℝ M y₀ (HasFDerivWithinAt.unique_on). So fderivWithin ℝ f M y₀ v = L₀ v for every v ∈ tangentConeAt ℝ M y₀.
5. (A₀a is in the tangent cone.) ψ has derivative A₀ at x₀, hence also within V at x₀. Since V ∈ 𝓝 x₀, tangentConeAt ℝ V x₀ = ℝⁿ (tangentConeAt_of_mem_nhds), so a ∈ tangentConeAt ℝ V x₀. By HasFDerivWithinAt.mapsTo_tangent_cone, A₀a ∈ tangentConeAt ℝ (ψ '' V) y₀. Since ψ '' V ⊆ M, tangentConeAt_mono gives A₀a ∈ tangentConeAt ℝ M y₀. [Directly: with c_k := k and d_k := ψ(x₀ + a/k) − y₀, we have y₀ + d_k ∈ ψ(V) ⊆ M for large k, d_k → 0 and c_k d_k → A₀a.]
6. (Conclusion.) By steps 4 and 5 with v := A₀a: fderivWithin ℝ f M (ψ x₀) (fderiv ℝ ψ x₀ a) = fderiv ℝ g (ψ x₀) (fderiv ℝ ψ x₀ a). ∎

## Key steps

1. ψ(x₀) ∈ M, hence f(ψ x₀) = g(ψ x₀).
2. HasFDerivWithinAt f (Dg(ψ x₀)) M (ψ x₀), by congruence with g.
3. fderivWithin ℝ f M (ψ x₀) is also a derivative of f within M.
4. Derivatives within M agree on the tangent cone (unique_on).
5. Dψ(x₀)a lies in the tangent cone of M at ψ(x₀) (mapsTo_tangent_cone, tangentConeAt_of_mem_nhds, tangentConeAt_mono).

## Reference use

### local-project

Queries:
- `cat nodes/root-stationary-results-a1-sff-chart-a1/{parent-child-handoff.json,parent-supplied-plan.md,parent-supplied-natural-proof.md}; cat problem.md; cat local-references/ff09f3909baeeae7/manifest.json`
- `python3 -I dag.json listing (id/status/lean_name; lean_statement of root.submanifold_tangent-a1 and its 5 children, root.stationary_results-a1.sff_chart-a1, sff_properties-a1)`
- `cat simongmt/Poincare/SimonGMT/Chapter02/{Submanifold,SubmanifoldTopology}.lean; diff snapshot project/GMT/Ch02/{Contract,Submission}.lean against workspace GMT/Ch02 (identical)`
- `sed -n 1,600p verifier/gmt-compare.py (contract_scope, child_modules, candidate_inputs, frozen_inputs); cat verifier/lean_contract.py`
- `grep -rn "theorem HasStrictFDerivAt.to_localInverse\|def HasStrictFDerivAt.localInverse\|theorem HasStrictFDerivAt.eventually_left_inverse\|theorem ContDiffAt.hasStrictFDerivAt\|exists_leftInverse_of_injective\|theorem eq_starProjection_of_mem_of_inner_eq_zero\|starProjection_eq_self_iff\|theorem differentiableAt_inverse\|theorem hasFDerivAt_ringInverse\|theorem HasFDerivAt.clm_apply\|theorem DifferentiableAt.clm_comp\|mapsTo_tangent\|theorem tangentConeAt_mono\|theorem tangentConeAt_of_mem_nhds\|theorem HasFDerivWithinAt.unique_on\|theorem Filter.EventuallyEq.eq_of_nhdsWithin\|theorem HasFDerivWithinAt.congr_of_eventuallyEq\|theorem ContDiffAt.fderiv_right" Mathlib --include=*.lean`
- `sed -n 100,215p Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean; sed -n 40,75p Mathlib/Analysis/Calculus/ContDiff/RCLike.lean; sed -n 395,430p Mathlib/Analysis/Calculus/FDeriv/Equiv.lean; sed -n 150,175p Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `grep -n "^theorem\|^def\|^lemma" Mathlib/Analysis/InnerProductSpace/Adjoint.lean; grep -rn adjoint Mathlib --include=*.lean | grep -i "differentiab\|hasFDeriv\|contDiff\|isBoundedLinearMap" (no match)`
- `grep -rn "isUnit_iff_bijective\|mul_inverse_cancel\|unitsEquiv\|class HasOrthogonalProjection\|Units.isOpen" Mathlib --include=*.lean`
- `lake build GMT.Ch02.Submission (scratch /tmp/sff-chart-decomp, .lake/packages -> lake-packages-25730c7c); python3 -I /tmp/sff-scripts/gen_checks.py (gmt-compare.child_modules + lean_contract.validate_lean_statement + dag.json collision check); lake env lean NodeChallenge_00..04.lean`
- `lake env lean AssemblyCheck.lean; lake env lean ProofCheck1.lean ProofCheck2.lean ProofCheck3.lean ProofCheck45.lean EndToEnd.lean (#print axioms)`
- `grep -rn <each proposed lean_name> project mathlib/Mathlib simongmt/Poincare --include=*.lean; grep -c '"<lean_name>"' dag.json`
- `sed -n 1060,1125p book/chapter-02.txt (printed Simon 4.23-4.27)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Equiv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/TangentCone/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/LinearAlgebra/Basis/VectorSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Algebra/GroupWithZero/Units/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Algebra/Module/Equiv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/NhdsWithin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldTopology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1-sff-chart-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1-sff-chart-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/sff-chart-decomp/AssemblyCheck.lean`
- `/tmp/sff-chart-decomp/EndToEnd.lean`

The snapshot contract is byte-identical to the workspace's GMT/Ch02/Contract.lean and Submission.lean. It defines B := fderivWithin ℝ (tangentProjection M) M y and tangentProjection := (tangentSpace M y).starProjection. Submission may add imports and new files under GMT/Ch02/; only Contract and the lake inputs are byte-frozen (gmt-compare.candidate_inputs). So the SimonGMT lemma IsSimonLocalRepresentation.exists_open_image_eq_inter (SubmanifoldTopology.lean, Simon 4.2) is usable.

Mathlib 25730c7c supplies everything the children need:
- HasStrictFDerivAt.localInverse / eventually_left_inverse / to_localInverse.
- ContDiffAt.hasStrictFDerivAt (side condition n ≠ 0) and ContDiffAt.fderiv_right.
- LinearMap.exists_leftInverse_of_injective.
- Submodule.eq_starProjection_of_mem_of_inner_eq_zero and starProjection_eq_self_iff.
- ContinuousLinearMap.adjoint_comp_self_injective_iff.
- differentiableAt_inverse, Ring.mul_inverse_cancel and Units.isOpen.
- HasFDerivAt.clm_apply and DifferentiableAt.clm_comp.
- HasFDerivWithinAt.unique_on, congr_of_eventuallyEq and mapsTo_tangent_cone.
- tangentConeAt_of_mem_nhds, tangentConeAt_mono and Filter.EventuallyEq.eq_of_nhdsWithin.
There is no ℝ-linear CLM form of ContinuousLinearMap.adjoint and no differentiability lemma for it (no-match), so the child builds one by hand. HasOrthogonalProjection is Prop-valued.

The five lean_statements validate and elaborate in the replayed comparator scope. AssemblyCheck derives the verbatim frozen parent type from them. EndToEnd.lean contains real proofs of all five children plus the glue, with axioms [propext, Classical.choice, Quot.sound].

None of the five lean_names occurs in dag.json, the project, SimonGMT or Mathlib. Simon's printed 4.26 says only "by a similar argument", so there is no printed proof to copy.
