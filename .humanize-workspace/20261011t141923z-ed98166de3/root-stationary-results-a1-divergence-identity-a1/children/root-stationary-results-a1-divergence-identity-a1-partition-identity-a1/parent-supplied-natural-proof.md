# Parent-supplied natural-language proof

- Parent DAG node: `root.stationary_results-a1.divergence_identity-a1`
- Child DAG node: `root.stationary_results-a1.divergence_identity-a1.partition_identity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3c of the supplied proof of the parent node root.stationary_results-a1.divergence_identity-a1 (Y = Σ_q ζ_q Y near every point of M, hence DY(y) = Σ_q D(ζ_q Y)(y) and div_M is additive), stated for arbitrary C¹ functions ζ_q with Σ_q ζ_q = 1 on an open O ⊇ M ∩ S.

Notation:
- τ_i := tangentFrame M y i, a finite family of vectors.
- div_M X(y) := tangentialDivergence M X y = Σ_i ⟨τ_i, DX(y)τ_i⟩, where DX(y) := fderiv ℝ X y.
- H := meanCurvature M.
- Y_q := ζ_q Y = (z ↦ ζ_q(z) Y(z)).

1. (Local decomposition.) Fix y ∈ M. Claim: Y(z) = Σ_q ζ_q(z) Y(z) for all z in a neighbourhood of y.
 - Case y ∈ S: then y ∈ M ∩ S ⊆ O, and O is open, so O is a neighbourhood of y. For z ∈ O, Σ_q ζ_q(z) Y(z) = (Σ_q ζ_q(z)) Y(z) = 1 · Y(z) = Y(z) (Finset.sum_smul).
 - Case y ∉ S: S is closed, so Sᶜ is an open neighbourhood of y. For z ∈ Sᶜ, Y(z) = 0, hence Σ_q ζ_q(z) Y(z) = Σ_q ζ_q(z) · 0 = 0 = Y(z).
 In both cases Y =ᶠ[𝓝 y] Σ_q Y_q.

2. (Derivative.) Each Y_q is C¹, as the product of the C¹ scalar function ζ_q and the C¹ field Y (ContDiff.smul), hence differentiable at y. By step 1 and Filter.EventuallyEq.fderiv_eq, and since the derivative of a finite sum of functions differentiable at y is the sum of their derivatives (fderiv_fun_sum / HasFDerivAt.sum): DY(y) = D(Σ_q Y_q)(y) = Σ_q DY_q(y).

3. (Divergence.) Use step 2, evaluation of a sum of linear maps, linearity of the inner product in its second argument (inner_sum) and exchange of finite sums (Finset.sum_comm):
 div_M Y(y) = Σ_i ⟨τ_i, (Σ_q DY_q(y)) τ_i⟩ = Σ_i Σ_q ⟨τ_i, DY_q(y) τ_i⟩ = Σ_q Σ_i ⟨τ_i, DY_q(y) τ_i⟩ = Σ_q div_M Y_q(y).

4. (Mean-curvature term.) Evaluating the eventual equality of step 1 at y itself gives Y(y) = Σ_q ζ_q(y) Y(y). Hence ⟨Y(y), H(y)⟩ = Σ_q ⟨ζ_q(y) Y(y), H(y)⟩ (sum_inner).

5. (Conclusion.) Add steps 3 and 4 and regroup the finite sums (Finset.sum_add_distrib): div_M Y(y) + ⟨Y(y), H(y)⟩ = Σ_q (div_M(ζ_q Y)(y) + ⟨ζ_q(y) Y(y), H(y)⟩). ∎

## Key steps

1. For y ∈ M, Y = Σ_q ζ_q Y on a neighbourhood of y: on O if y ∈ S (where Σ_q ζ_q = 1), and on Sᶜ if y ∉ S (where both sides vanish).
2. Hence DY(y) = Σ_q D(ζ_q Y)(y), by EventuallyEq.fderiv_eq and the derivative of a finite sum of differentiable maps.
3. Linearity of the frame sum gives div_M Y(y) = Σ_q div_M(ζ_q Y)(y). The identity Y(y) = Σ_q ζ_q(y)Y(y) gives the ⟨·, H⟩ term. Add the two.

## Reference use

### local-project

Queries:
- `cat -n GMT/Ch02/Contract.lean; cat GMT/Ch02/README.md (snapshot project; checked that no SimonGMT tool used here is flagged unfaithful)`
- `grep -n 'theorem\|def ' simongmt/Poincare/SimonGMT/Chapter02/{Submanifold,SubmanifoldCalculus,SubmanifoldIntegral,SubmanifoldTopology,WeightedArea,Area}.lean`
- `grep -rn 'integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable|euclideanHausdorffMeasure_eq_volume|setIntegral_eq_of_subset_of_forall_sdiff_eq_zero|finrank_euclideanSpace_fin|IntegrableOn.of_forall_sdiff_eq_zero|integrableOn_of_bounded|trace_eq_sum_inner|exists_isSubordinate' mathlib/Mathlib`
- `grep ContDiffBump API (one_of_mem_closedBall, tsupport_eq, hasCompactSupport, contDiff); prod_one_sub_ordered; IsCompact.elim_nhds_subcover; contDiff_prod; HasCompactSupport.fderiv_apply; integral_finsetSum; setIntegral_eq_integral_of_forall_compl_eq_zero; basisFun_inner`
- `rg for the five proposed lean_names in project/, mathlib/Mathlib, simongmt/Poincare and all 234 git refs (GMT/*.lean); python3 -I collision check against dag.json (119 nodes)`
- `python3 -I gen_checks.py: gmt-compare.py child_modules (contract scope) + lean_contract.validate_lean_statement for the 5 statements; lake env lean NodeChallenge_00..04.lean`
- `lake env lean checks/AssemblyCheck.lean, C1Check..C5Check.lean, FullCheck.lean with #print axioms; ImportProbe.lean; pp.all #print diff of the 36 contract definitions with/without extra imports (PrintA vs PrintB)`
- `sed -n 1040,1160p book/chapter-02.txt (printed 4.20-4.30); read dag.json and nodes/root-stationary-results-a1-divergence-identity-a1/parent-child-handoff.json and parent-supplied-plan.md; git show of accepted-node Submission.lean headers`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Trace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Algebra/BigOperators/Ring/Finset.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Const.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldTopology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1-divergence-identity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/divid-decomp/checks/AssemblyCheck.lean`
- `/tmp/divid-decomp/checks/FullCheck.lean`

Frozen contract (Contract.lean lines 83-176): tangentialDivergence is the frame sum, meanCurvature is the frame trace of B, and tangentProjection is starProjection. The README marks none of the SimonGMT tools used here as unfaithful.

SimonGMT supplies kernel-checked tools:
- integral_area_formula_of_injective_derivative (WeightedArea.lean): a Bochner area formula with no integrability hypothesis;
- submanifoldDivergenceAt_eq_sum_inner (SubmanifoldCalculus.lean);
- areaJacobianAt (Area.lean).
SimonGMT has no submanifold divergence theorem: integral_submanifoldDivergence_eq_curvature_sub_boundary takes the tangential divergence theorem as a hypothesis. So the five children are new obligations.

Mathlib 25730c7c supplies:
- integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (LineDeriv/IntegrationByParts.lean);
- EuclideanSpace.euclideanHausdorffMeasure_eq_volume;
- setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (the _diff name is deprecated);
- IntegrableOn.of_forall_sdiff_eq_zero;
- integral_finsetSum (integral_finset_sum is deprecated);
- LinearMap.trace_eq_sum_inner;
- ContDiffBump.{one_of_mem_closedBall, tsupport_eq, hasCompactSupport, contDiff};
- Finset.prod_one_sub_ordered;
- IsCompact.elim_nhds_subcover;
- HasCompactSupport.fderiv_apply.
The manifold and topological partitions of unity (exists_isSubordinate) were checked and are not needed.

Compile checks:
- All 5 statements validate and elaborate in the replayed contract scope.
- AssemblyCheck.lean proves the frozen parent type from the children and the sibling types.
- FullCheck.lean proves every child with only propext, Classical.choice and Quot.sound.
- Extra imports leave all frozen definitions byte-identical under pp.all.
- No lean_name collisions.
