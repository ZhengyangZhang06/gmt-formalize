# Parent-supplied natural-language proof

- Parent DAG node: `root.coarea_formula-a1`
- Child DAG node: `root.coarea_formula-a1.chart_coarea-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 3 of the parent proof.

Notation and standard facts.
- P := WithLp 2 (ℝᵐ × ℝᵏ) is an inner product space with finrank_ℝ P = m + k.
- toLp(a,b) ∈ P for a ∈ ℝᵐ, b ∈ ℝᵏ; p₁ := WithLp.fst p and p₂ := WithLp.snd p.
- (a,b) ↦ toLp(a,b) is measure preserving from volume on ℝᵐ × ℝᵏ (= Lᵐ ⊗ Lᵏ) to volume on P (WithLp.volume_preserving_toLp).
- On every finite-dimensional inner product space E, μHE[finrank E] = volume (InnerProductSpace.euclideanHausdorffMeasure_eq_volume), and finrank ℝᵏ = k.
- j : ℝᵏ → P, j(b) := toLp(0,b), is a linear isometry.
- For a ∈ ℝᵐ, the fibre map is Ψ_a(b) := Ψ(toLp(a,b)) and its domain is Ω_a := {b : toLp(a,b) ∈ Ω}, which is open.
- For p ∈ Ω put J(p) := normDet(DΨ(p)) = areaJacobianAt Ψ p and J_v(p) := normDet(DΨ(p) ∘ j).
- J*f := coareaJacobian M f ≥ 0, since it is a real square root.

1. Derivatives.
   - For p ∈ Ω, Ψ is differentiable at p (C¹ on the open set Ω).
   - For b ∈ Ω_a, the map b ↦ toLp(a,b) = toLp(a,0) + j(b) is affine with derivative j. So Ψ_a is differentiable at b with DΨ_a(b) = DΨ(toLp(a,b)) ∘ j. This map is injective because j and DΨ are injective, and Ψ_a is injective on Ω_a.
   - f ∘ Ψ coincides on the open set Ω with the continuous linear map p ↦ p₁, so D(f ∘ Ψ)(p) = (q ↦ q₁). Since f is differentiable at Ψ(p), the chain rule gives Df(Ψ p)(DΨ(p) q) = q₁ for all q ∈ P.
2. Pointwise Jacobian identity. Let p = toLp(a,b) ∈ Ω. Apply child coarea_jacobian_linear_algebra part (2) with:
   - x := Ψ(p);
   - A := DΨ(p), which is injective, has range tangentSpace M (Ψ p) by hypothesis, and satisfies Df(x)(A q) = q₁ by step 1;
   - B := DΨ_a(b), which satisfies B b′ = A(toLp(0,b′)) by step 1.
   It gives J*f(Ψ p)·J(p) = normDet(DΨ_a(b)) = J_v(p).
3. Pull-back of the left side. S′ := Ω ∩ Ψ⁻¹(S) is a Borel subset of P (Ψ is continuous on the open set Ω, and S is Borel). Since S ⊆ Ψ(Ω), Ψ(S′) = S. Apply SimonGMT weighted_area_formula_volume_of_injective_derivative with E := P, s := S′, the map Ψ (differentiable with injective derivative on S′ and injective on S′) and the weight w(x) := g(x)·ofReal(J*f(x)). Since finrank P = m + k,
   ∫_S g·ofReal(J*f) dμHE[m+k] = ∫_{S′} ofReal(J(p))·g(Ψ p)·ofReal(J*f(Ψ p)) dp = ∫_P H(p) dp,
   where H(p) := 1_{S′}(p)·g(Ψ p)·ofReal(J_v(p)). The last equality uses step 2 and ofReal(J*f(Ψp))·ofReal(J(p)) = ofReal(J*f(Ψp)·J(p)), valid because both factors are ≥ 0.
4. H is Borel.
   - p ↦ DΨ(p) is Borel (measurable_fderiv); composing with j is continuous, and normDet is continuous (SimonGMT continuous_normDet). So J_v is Borel.
   - Ψ is continuous on the open (hence Borel) set Ω, so p ↦ 1_Ω(p)·g(Ψ p) is Borel.
   - S′ ⊆ Ω is Borel.
   Hence H is Borel.
5. Tonelli. Using the measure-preserving map toLp and Tonelli on ℝᵐ × ℝᵏ (lintegral_prod), ∫_P H dp = ∫_{ℝᵐ} F(a) da, where F(a) := ∫_{ℝᵏ} H(toLp(a,b)) db. F is Borel by Measurable.lintegral_prod_right', applied to the Borel function (a,b) ↦ H(toLp(a,b)).
6. Fibrewise area formula. Fix a ∈ ℝᵐ and let S′_a := {b : toLp(a,b) ∈ S′}, a Borel subset of Ω_a.
   Claim: Ψ_a(S′_a) = S ∩ f⁻¹{a}.
   - If b ∈ S′_a, then Ψ_a(b) = Ψ(toLp(a,b)) ∈ S and f(Ψ_a(b)) = (toLp(a,b))₁ = a.
   - Conversely, let x ∈ S with f(x) = a. Then x = Ψ(p) for some p ∈ Ω (because S ⊆ Ψ(Ω)), so p ∈ S′. Also a = f(Ψ p) = p₁, so p = toLp(a, p₂), p₂ ∈ S′_a and Ψ_a(p₂) = x.
   Now apply SimonGMT weighted_area_formula_volume_of_injective_derivative with E := ℝᵏ, s := S′_a, the map Ψ_a (differentiable with injective derivative on S′_a ⊆ Ω_a and injective there, by step 1) and the weight g:
   ∫_{S∩f⁻¹{a}} g dμHE[k] = ∫_{S′_a} ofReal(normDet DΨ_a(b))·g(Ψ_a b) db = ∫_{ℝᵏ} H(toLp(a,b)) db = F(a).
   The middle equality holds because normDet DΨ_a(b) = J_v(toLp(a,b)) for b ∈ S′_a (step 1), and H(toLp(a,b)) = 0 for b ∉ S′_a.
7. Conclusion. By step 6, y ↦ ∫_{S∩f⁻¹{y}} g dμHE[k] equals F at every point, so it is Borel by step 5. By steps 3, 5 and 6,
   ∫_S g·J*f dμHE[m+k] = ∫_P H = ∫_{ℝᵐ} F(a) da = ∫_{ℝᵐ} ∫_{S∩f⁻¹{a}} g dμHE[k] da.

## Key steps

1. Chain rule on the open set Ω: Df(Ψp)∘DΨ(p) is the first-component map, and the fibre map Ψ_a(b) = Ψ(toLp(a,b)) has DΨ_a(b) = DΨ(toLp(a,b))∘j.
2. Child part (2) gives J*f(Ψp)·normDet DΨ(p) = normDet DΨ_a(b) pointwise on Ω.
3. The weighted area formula for Ψ on S′ = Ω∩Ψ⁻¹S turns ∫_S g·J*f dμHE[m+k] into ∫_P 1_{S′}·g(Ψ)·normDet(DΨ∘j).
4. Tonelli through WithLp.volume_preserving_toLp writes this as ∫_a ∫_b, with the inner integral Borel in a.
5. The fibrewise area formula for Ψ_a on S′_a, with Ψ_a(S′_a) = S∩f⁻¹{a}, identifies the inner integral with ∫_{S∩f⁻¹{a}} g dμHE[k] for every a.

## Reference use

### local-project

Queries:
- `rg -il 'coarea' mathlib/Mathlib`
- `rg -n 'theorem .*[Ss]ard' mathlib/Mathlib`
- `rg -n 'def coareaJacobian|def tangentSpace|def CoareaFormula|def C1Sard' project/GMT/Ch02/Contract.lean`
- `rg -n 'Submission\.' project`
- `rg -n 'theorem hausdorffMeasure_apply|theorem MeasureTheory.Measure.euclideanHausdorffMeasure_def|theorem euclideanHausdorffMeasure_eq_volume' mathlib/Mathlib`
- `rg -n 'theorem lintegral_liminf_le |theorem measurable_fderiv |theorem ContDiffOn.exists_lipschitzOnWith|def toOpenPartialHomeomorph|theorem OpenPartialHomeomorph.contDiffAt_symm|theorem WithLp.volume_preserving_toLp|theorem isOpen_iUnion_countable|theorem exists_surjective_nat|theorem normDet_comp |theorem normDet_codRestrict|theorem _root_.ContinuousLinearMap.normDet_sq' mathlib/Mathlib`
- `grep -n '^theorem\|^def' mathlib/Mathlib/Analysis/Calculus/Implicit.lean`
- `grep -rn 'theorem iUnion_disjointed\|theorem disjoint_disjointed\|theorem MeasurableSet.disjointed\|theorem lintegral_iUnion\|theorem lintegral_tsum\|theorem lintegral_union\|theorem setLIntegral_measure_zero\|theorem ContDiffOn.differentiableOn' mathlib/Mathlib`
- `grep -n '^theorem\|^lemma\|^def\|^noncomputable def' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/*.lean`
- `#print axioms for Chapter02.weighted_area_formula_of_injective_derivative, weighted_area_formula_volume_of_injective_derivative, IsSimonLocalRepresentation.exists_open_image_eq_inter, coareaLinearJacobian_eq_zero_iff, coareaLinearJacobian_eq_sqrt_det, coareaHorizontalLinear_normDet, euclideanHausdorffMeasure_image_le_of_lipschitzOn, continuous_normDet, measurable_areaJacobianAt, coarea_projection_lintegral, coarea_linear_lintegral`
- `python3 -I gen_checks.py (verifier gmt-compare.py child_modules/contract_scope + lean_contract.validate_lean_statement on the six statements); lean NodeChallenge_00..05.lean against a scratch olean of GMT.Ch02.Submission`
- `lean FinalAssembly.lean (sorried stand-ins of the six child types and the frozen simon_submanifold_tangent_basics type; sorry-free check_C, check_F, check_parent : CoareaFormula; #print axioms)`
- `lean SkeletonE.lean; lean Inst.lean (#synth InnerProductSpace ℝ (WithLp 2 (Rn m × Rn k))); python3 -I lemmaL2.py`
- `python3 -I: list lean_name of every node in dag.json`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/Implicit.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Order/Disjointed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Normed/Lp/ProdLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldTopology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinearAlgebra.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaProjection.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCritical.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-coarea-formula-a1/parent-child-handoff.json`
- `/tmp/coarea-decomp-94z3yF/check/FinalAssembly.lean`
- `/tmp/coarea-decomp-94z3yF/check/SkeletonE.lean`

Nothing in the snapshot proves the nonlinear co-area formula or a Sard-type theorem: rg -il coarea over mathlib/Mathlib finds no file, and rg 'theorem .*[Ss]ard' finds no match.

project/GMT/Ch02/Contract.lean fixes tangentSpace (l.86), coareaJacobian (l.123: √det(L∘L†) with L = fderiv f x ∘ subtypeL), CoareaFormula (l.349) and C1Sard (l.362). The project has no Submission.* declarations.

Mathlib supplies:
- the normDet API (NormDet.lean: ContinuousLinearMap.normDet_sq l.267, normDet_comp l.324, normDet_codRestrict l.365, normDet_eq_norm_det_toMatrix);
- μHE = c·μH (Measure.lean l.74) and hausdorffMeasure_apply (Hausdorff.lean l.546);
- the C¹ inverse function theorem (InverseFunctionTheorem/ContDiff.lean l.31; OpenPartialHomeomorph.contDiffAt_symm, Operations.lean l.881) and the implicit-function version (Implicit.lean l.457);
- measurable_fderiv (FDeriv/Measurable.lean l.378) and ContDiffOn.exists_lipschitzOnWith (RCLike.lean l.149);
- WithLp.volume_preserving_toLp (Haar/InnerProductSpace.lean l.211), lintegral_prod, lintegral_liminf_le (Lebesgue/Add.lean l.233), lintegral_iUnion/lintegral_tsum, disjointed, TopologicalSpace.isOpen_iUnion_countable (Bases.lean l.932) and exists_surjective_nat.

The pinned SimonGMT package supplies:
- weighted_area_formula_(volume_)of_injective_derivative (WeightedArea.lean);
- IsSimonLocalRepresentation.exists_open_image_eq_inter (Simon 4.2, SubmanifoldTopology.lean);
- coareaLinearJacobian_eq_zero_iff, coareaLinearJacobian_eq_sqrt_det and coareaHorizontalLinear_normDet (CoareaLinearAlgebra.lean);
- euclideanHausdorffMeasure_image_le_of_lipschitzOn (Lipschitz.lean) and continuous_normDet (AreaApproximation.lean).
#print axioms reports only propext, Classical.choice and Quot.sound for all of them. These modules are not imported by the contract, so children must add the imports, which the comparator permits.

No node in dag.json reserves any of the six proposed bare names.

All six statements pass validate_lean_statement and elaborate in the comparator's replayed contract scope. The six generated NodeChallenge modules compile. #synth confirms that WithLp 2 (Rn m × Rn k) carries WithLp.instProdInnerProductSpace.

In FinalAssembly.lean, Lean accepts sorry-free proofs of coarea_critical_fibers_null, coarea_formula_of_measurable and CoareaFormula from sorried stand-ins of exactly the child types and of the frozen sibling type. The split therefore implies the selected parent.
