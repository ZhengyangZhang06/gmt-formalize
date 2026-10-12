# Parent-supplied natural-language proof

- Parent DAG node: `root.stationary_results-a1.sff_chart-a1`
- Child DAG node: `root.stationary_results-a1.sff_chart-a1.projection_field_identity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 8 (parent G2, the computation of L₀) of the supplied proof of second_fundamental_form_chart_formula. That step differentiates the identity P̃(ψ(x))(Dψ(x)b) = Dψ(x)b at x₀ in direction a. Here the operator field is an arbitrary Q with the fixing property.
Notation: y₀ := ψ(x₀); A(x) := Dψ(x) = fderiv ℝ ψ x; A₀ := A(x₀); L₀ := DQ(y₀) = fderiv ℝ Q y₀ ∈ L(ℝᴺ, L(ℝᴺ, ℝᴺ)); D := DA(x₀) = fderiv ℝ (fderiv ℝ ψ) x₀ ∈ L(ℝⁿ, L(ℝⁿ, ℝᴺ)), so that D²ψ(x₀)[a, b] = D a b. Fix a, b ∈ ℝⁿ.
1. (Chain rule.) ψ has derivative A₀ at x₀ and Q has derivative L₀ at y₀. So c(x) := Q(ψ(x)) ∈ L(ℝᴺ, ℝᴺ) has derivative L₀ ∘ A₀ at x₀ (HasFDerivAt.comp).
2. (Derivative of x ↦ A(x)b.) u(x) := A(x)b applies the operator-valued map A, which has derivative D at x₀, to the constant vector b, which has derivative 0. By the product rule for applying an operator-valued map to a vector-valued map (HasFDerivAt.clm_apply), u has derivative u′ := A₀ ∘ 0 + D.flip b at x₀. That is, u′(a′) = D a′ b for a′ ∈ ℝⁿ.
3. (Product rule for G.) Let G(x) := c(x)(u(x)) = Q(ψ(x))(A(x)b). By HasFDerivAt.clm_apply applied to steps 1 and 2, G has derivative G′ := c(x₀) ∘ u′ + (L₀ ∘ A₀).flip (u(x₀)) at x₀. That is, G′(a′) = Q(y₀)(D a′ b) + L₀(A₀a′)(A₀b).
4. (G = u near x₀.) By hypothesis with v := b, G(x) = Q(ψ(x))(A(x)b) = A(x)b = u(x) for all x in a neighbourhood of x₀. So u′ is also a derivative of G at x₀ (HasFDerivAt.congr_of_eventuallyEq). By uniqueness of the Fréchet derivative (HasFDerivAt.unique), G′ = u′. Evaluating at a′ = a gives Q(y₀)(D a b) + L₀(A₀a)(A₀b) = D a b.
5. (Rearranging.) L₀(A₀a)(A₀b) = D a b − Q(y₀)(D a b), i.e. fderiv ℝ Q (ψ x₀) (fderiv ℝ ψ x₀ a) (fderiv ℝ ψ x₀ b) = fderiv ℝ (fderiv ℝ ψ) x₀ a b − Q (ψ x₀) (fderiv ℝ (fderiv ℝ ψ) x₀ a b). ∎

## Key steps

1. Chain rule: D(Q ∘ ψ)(x₀) = DQ(ψ x₀) ∘ Dψ(x₀).
2. D(x ↦ Dψ(x)b)(x₀)a = D²ψ(x₀)[a, b] (clm_apply with a constant vector).
3. Product rule (clm_apply) for x ↦ Q(ψ x)(Dψ(x)b).
4. This map equals x ↦ Dψ(x)b near x₀, and Fréchet derivatives are unique.
5. Evaluate at a and rearrange.

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
