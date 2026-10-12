# Parent-supplied natural-language proof

- Parent DAG node: `root.stationary_results-a1.divergence_identity-a1`
- Child DAG node: `root.stationary_results-a1.divergence_identity-a1.integrability-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 0(b)–0(d) and 1 of the supplied proof of the parent node root.stationary_results-a1.divergence_identity-a1. The facts that the parent derives from (TH2), the sibling sff_properties and the sibling measure_bounds are taken here as hypotheses: measurability of M, continuity of P and H on M, and finiteness of μHE[n] on compact subsets of M.

Notation:
- ℝᴺ = EuclideanSpace ℝ (Fin N), and Hⁿ := μHE[n] on ℝᴺ.
- T_y := tangentSpace M y, and P_y := tangentProjection M y = T_y.starProjection, the orthogonal projection onto T_y.
- τ_i := tangentFrame M y i = (stdOrthonormalBasis ℝ T_y) i.
- div_M Y(y) := tangentialDivergence M Y y = Σ_i ⟨τ_i, DY(y)τ_i⟩, where DY(y) := fderiv ℝ Y y.
- H := meanCurvature M.

1. (Trace formula.) For every y ∈ ℝᴺ, div_M Y(y) = trace(DY(y) ∘ P_y).
 Proof. SimonGMT's Poincare.SimonGMT.Chapter02.submanifoldDivergenceAt_eq_sum_inner (module Poincare.SimonGMT.Chapter02.SubmanifoldCalculus), with T := T_y and the orthonormal basis b := stdOrthonormalBasis ℝ T_y, states trace(DY(y) ∘ T_y.starProjection) = submanifoldDivergenceAt T_y Y y = Σ_i ⟨b_i, DY(y) b_i⟩. The right side is by definition div_M Y(y), since tangentFrame M y i = b_i.
 Direct argument: let ι : T_y → ℝᴺ be the inclusion and π : ℝᴺ → T_y the orthogonal projection, so P_y = ι ∘ π. By cyclicity of the trace and orthonormality, trace(DY(y) ∘ ι ∘ π) = trace_{T_y}(π ∘ DY(y) ∘ ι) = Σ_i ⟨τ_i, π(DY(y)τ_i)⟩ = Σ_i ⟨τ_i, DY(y)τ_i⟩.

2. (Continuity of f₁ := div_M Y on M.)
 - y ↦ DY(y) is continuous on ℝᴺ because Y is C¹ (ContDiff.continuous_fderiv).
 - y ↦ P_y is continuous on M by hypothesis.
 - Composition of continuous linear maps is jointly continuous, so y ↦ DY(y) ∘ P_y is continuous on M (ContinuousOn.clm_comp).
 - The map A ↦ trace(A) on the finite-dimensional space of linear maps of ℝᴺ is linear, hence continuous (LinearMap.continuous_of_finiteDimensional, applied to the trace composed with the linear coercion ContinuousLinearMap.coeLM).
 By step 1, f₁ is continuous on M.

3. (Continuity of f₂ := y ↦ ⟨Y(y), H(y)⟩ on M.) Y is continuous, H is continuous on M by hypothesis, and the inner product is continuous, so f₂ is continuous on M (ContinuousOn.inner).

4. (Vanishing off F.) Let y ∉ F. The set Fᶜ is open (F is closed), contains y, and Y ≡ 0 on Fᶜ. Hence Y =ᶠ[𝓝 y] 0 and DY(y) = 0 (Filter.EventuallyEq.fderiv_eq). Therefore f₁(y) = Σ_i ⟨τ_i, 0⟩ = 0 and f₂(y) = ⟨0, H(y)⟩ = 0.

5. (Integrability criterion.) Let f : ℝᴺ → ℝ be continuous on M with f(y) = 0 for y ∈ M ∖ F. Then f is integrable on M with respect to Hⁿ:
 (a) f is continuous on the compact set M ∩ F, so there is a constant C with |f| ≤ C on M ∩ F (IsCompact.exists_bound_of_continuousOn).
 (b) M ∩ F is compact, hence closed, hence measurable, and f is a.e.-strongly measurable for Hⁿ restricted to M ∩ F (ContinuousOn.aestronglyMeasurable).
 (c) Hⁿ(M ∩ F) < ∞ by hypothesis, because M ∩ F ⊆ M is compact. This must come from the hypothesis: Hⁿ = μHE[n] is in general not finite on compact subsets of ℝᴺ when n < N.
 (d) By (a)–(c), f is integrable on M ∩ F, being a bounded a.e.-strongly measurable function on a set of finite measure: ∫_{M∩F}|f| ≤ C·Hⁿ(M ∩ F) < ∞ (HasFiniteIntegral.restrict_of_bounded).
 (e) Since M is measurable and f = 0 on M ∖ (M ∩ F) = M ∖ F, f is integrable on M (IntegrableOn.of_forall_sdiff_eq_zero).

6. (Conclusion.) By steps 2–4, f₁ and f₂ satisfy the assumptions of step 5, so both are integrable on M with respect to μHE[n]. ∎

Implementation note: submanifoldDivergenceAt_eq_sum_inner requires `import Poincare.SimonGMT.Chapter02.SubmanifoldCalculus`, which was checked to leave the frozen definitions byte-identical. Alternatively, prove step 1 directly from LinearMap.trace_comp_comm' and LinearMap.trace_eq_sum_inner, as in the direct argument.

## Key steps

1. div_M Y(y) = trace(DY(y) ∘ P_y) (SimonGMT submanifoldDivergenceAt_eq_sum_inner with the frame basis), so div_M Y is continuous on M; ⟨Y, H⟩ is also continuous on M.
2. Both functions vanish at every y ∉ F, because Y ≡ 0 on the open neighbourhood Fᶜ, so DY(y) = 0.
3. A function continuous on M and zero on M ∖ F is bounded on the compact set M ∩ F and a.e.-strongly measurable there, and Hⁿ(M ∩ F) < ∞; so it is integrable on M ∩ F, and hence on the measurable set M.

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
