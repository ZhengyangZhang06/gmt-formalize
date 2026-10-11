# Parent-supplied natural-language proof

- Parent DAG node: `root.coarea_formula-a1.chart_coarea-a1`
- Child DAG node: `root.coarea_formula-a1.chart_coarea-a1.chart_fiber_disintegration-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 1 (fibre-map part), 4, 5, 6 and 7 of the selected node's supplied proof. The intermediate integral ∫_P H dp of that proof is written here as the set integral over S′ = Ω ∩ Ψ⁻¹(S).

Notation.
- P := WithLp 2 (ℝᵐ × ℝᵏ) carries its inner-product-space volume dp.
- j : ℝᵏ → P is (WithLp.prodContinuousLinearEquiv 2 ℝ ℝᵐ ℝᵏ).symm ∘L inr, so j(b) = toLp(0,b) definitionally.
- normDet := LinearMap.normDet.
- S′ := Ω ∩ Ψ⁻¹(S) and J_v(p) := normDet(DΨ(p)∘j).
- G(p) := ofReal(J_v(p))·g(Ψ p) and H := 1_{S′}·G (Set.indicator).
- For a ∈ ℝᵐ: ι_a(b) := toLp(a,b), Ψ_a := Ψ∘ι_a : ℝᵏ → ℝᴺ, S′_a := ι_a⁻¹(S′) = {b : toLp(a,b) ∈ S′}, and F(a) := ∫_{ℝᵏ} H(toLp(a,b)) db.

1. j is injective: j(b) = toLp(0,b) and WithLp.snd(toLp(0,b)) = b.

2. Differentiability. For p ∈ Ω, Ψ is differentiable at p: it is C¹ on Ω (ContDiffOn.differentiableOn with 1 ≠ 0) and Ω is an open neighbourhood of p. Hence Ψ is continuous on Ω.

3. S′ is Borel. Ψ̃ := Ω.piecewise Ψ (fun _ ↦ 0) is Borel by ContinuousOn.measurable_piecewise: Ψ is continuous on Ω, the constant is continuous on Ωᶜ, and Ω is open, hence Borel. Since Ψ̃ = Ψ on Ω, S′ = Ω ∩ Ψ̃⁻¹(S) is Borel.

4. H is Borel.
(i) p ↦ DΨ(p) is Borel from P into the space of continuous linear maps (measurable_fderiv, valid for every function). L ↦ L∘j is continuous, L ↦ normDet(L) is continuous (SimonGMT Chapter02.continuous_normDet), and ofReal is measurable. So p ↦ ofReal(J_v(p)) is Borel on all of P.
(ii) g∘Ψ̃ is Borel, as a composite of Borel maps.
(iii) Ψ̃ = Ψ on S′ ⊆ Ω, so H = 1_{S′}·(ofReal(J_v)·g∘Ψ̃) (Set.indicator_congr). This is the indicator of a Borel set times a product of Borel functions, so H is Borel.

5. Tonelli. Let T : ℝᵐ × ℝᵏ → P, T(a,b) := toLp(a,b). T is measurable (WithLp.measurable_toLp). It is measure preserving from volume on ℝᵐ × ℝᵏ, which is the product measure volume ⊗ volume (Measure.volume_eq_prod), to volume on P (WithLp.volume_preserving_toLp). H∘T is Borel by 4. Therefore:
∫_{S′} G dp
= ∫_P H dp (lintegral_indicator; S′ is Borel)
= ∫_{ℝᵐ×ℝᵏ} H(T(a,b)) d(a,b) (MeasurePreserving.lintegral_comp; H is measurable)
= ∫_{ℝᵐ} F(a) da (lintegral_prod, i.e. Tonelli).
Moreover F is Borel, by Measurable.lintegral_prod_right' applied to H∘T.

6. Fibre derivative. Let a ∈ ℝᵐ and b ∈ ℝᵏ with toLp(a,b) ∈ Ω.
- b′ ↦ (a,b′) has derivative inr at b (hasFDerivAt_prodMk_right).
- toLp = (WithLp.prodContinuousLinearEquiv 2 ℝ ℝᵐ ℝᵏ).symm is continuous linear. So ι_a has derivative (prodContinuousLinearEquiv).symm ∘L inr = j at b.
- By 2 and the chain rule, Ψ_a has derivative DΨ(toLp(a,b))∘j at b.
So Ψ_a is differentiable at b and DΨ_a(b) = DΨ(toLp(a,b))∘j (HasFDerivAt.fderiv).

For steps 7–9, fix a ∈ ℝᵐ.

7. Hypotheses of the area formula on the fibre.
(i) S′_a is Borel. ι_a is continuous (b ↦ (a,b) followed by the continuous toLp), hence measurable, and S′ is Borel (3).
(ii) Let b ∈ S′_a. Then toLp(a,b) ∈ Ω, so by 6, Ψ_a is differentiable at b and DΨ_a(b) = DΨ(toLp(a,b))∘j. This map is injective: j is injective (1) and DΨ(toLp(a,b)) is injective (hypothesis).
(iii) Ψ_a is injective on S′_a. Let b, b′ ∈ S′_a with Ψ(toLp(a,b)) = Ψ(toLp(a,b′)). Both points toLp(a,b), toLp(a,b′) lie in Ω and Ψ is injective on Ω, so toLp(a,b) = toLp(a,b′). Applying WithLp.snd gives b = b′.

8. Image of the fibre: Ψ_a(S′_a) = S ∩ f⁻¹{a}.
(⊆) Let b ∈ S′_a and p := toLp(a,b) ∈ Ω ∩ Ψ⁻¹(S). Then Ψ_a(b) = Ψ(p) ∈ S. Also f(Ψ(p)) = WithLp.fst p = a, because p ∈ Ω.
(⊇) Let x ∈ S with f(x) = a. Since S ⊆ Ψ(Ω), x = Ψ(p) for some p ∈ Ω. Then p ∈ S′, and a = f(Ψ p) = WithLp.fst p. Hence p = toLp(WithLp.fst p, WithLp.snd p) = toLp(a, WithLp.snd p), which holds definitionally for WithLp. So b := WithLp.snd p lies in S′_a, and Ψ_a(b) = Ψ(p) = x.

9. Fibre area formula. Apply SimonGMT Chapter02.weighted_area_formula_volume_of_injective_derivative with E := ℝᵏ, F := ℝᴺ, s := S′_a, the map Ψ_a and the weight g. Its hypotheses hold by 7. Since finrank_ℝ ℝᵏ = k (finrank_euclideanSpace_fin), and by 8:
∫_{S∩f⁻¹{a}} g dμHE[k] = ∫_{S′_a} ofReal(areaJacobianAt Ψ_a b)·g(Ψ_a b) db.
For b ∈ S′_a, step 6 gives areaJacobianAt Ψ_a b = normDet(DΨ_a(b)) = normDet(DΨ(toLp(a,b))∘j) = J_v(toLp(a,b)). So the integrand equals G(toLp(a,b)).
Next, rewrite the set integral over the Borel set S′_a as the whole-space integral of 1_{S′_a}(b)·G(toLp(a,b)) (lintegral_indicator). Since 1_{S′_a}(b) = 1_{S′}(toLp(a,b)), comparing integrands pointwise (cases b ∈ S′_a and b ∉ S′_a) gives
∫_{S′_a} G(toLp(a,b)) db = ∫_{ℝᵏ} H(toLp(a,b)) db = F(a).
Hence ∫_{S∩f⁻¹{a}} g dμHE[k] = F(a) for every a ∈ ℝᵐ.

10. Conclusion.
- By 9, the function y ↦ ∫_{S∩f⁻¹{y}} g dμHE[k] equals F (funext). F is Borel by 5, which proves the first claim.
- By 5 and 9, ∫_{Ω∩Ψ⁻¹(S)} ofReal(normDet(DΨ(p)∘j))·g(Ψ p) dp = ∫_{S′} G dp = ∫_{ℝᵐ} F(a) da = ∫_{ℝᵐ} ∫_{S∩f⁻¹{a}} g dμHE[k] da. This is the second claim.

## Key steps

1. S′ := Ω∩Ψ⁻¹(S) is Borel. H := 1_{S′}·ofReal(normDet(DΨ∘j))·g∘Ψ is Borel, using measurable_fderiv, continuous_normDet and the piecewise extension of Ψ.
2. Tonelli through the measure-preserving toLp : ℝᵐ×ℝᵏ → P gives ∫_{S′} ofReal(normDet(DΨ∘j))·g∘Ψ = ∫_a F(a), with F(a) := ∫_b H(toLp(a,b)) Borel in a.
3. The fibre map Ψ_a := Ψ(toLp(a,·)) has derivative DΨ(toLp(a,b))∘j, which is injective. Ψ_a is injective on S′_a := {b : toLp(a,b) ∈ S′}, which is Borel.
4. Ψ_a(S′_a) = S∩f⁻¹{a}, because f∘Ψ = fst on Ω and S ⊆ Ψ(Ω).
5. The SimonGMT weighted area formula on ℝᵏ (finrank k) gives ∫_{S∩f⁻¹{a}} g dμHE[k] = F(a) for every a. This yields both the Borel measurability and the integral identity.

## Reference use

### local-project

Queries:
- `rg -n "theorem WithLp.volume_preserving_toLp|theorem InnerProductSpace.euclideanHausdorffMeasure_eq_volume|theorem measurable_fderiv |theorem Measurable.lintegral_prod_right'|theorem lintegral_prod |theorem hasFDerivAt_prodMk_right|def prodContinuousLinearEquiv|def fstL|theorem ContinuousOn.measurable_piecewise|theorem finrank_euclideanSpace_fin|theorem lintegral_indicator |theorem setLIntegral_congr_fun |theorem HasFDerivAt.congr_of_eventuallyEq|theorem HasFDerivAt.unique|theorem ofReal_mul " mathlib/Mathlib`
- `rg -n "theorem ContDiffOn.differentiableOn |theorem lintegral_comp \{f : β → ℝ≥0∞\} \(hf : Measurable f\) :|theorem volume_eq_prod|lemma measurable_toLp|lemma prodContinuousLinearEquiv_symm_apply" mathlib/Mathlib`
- `rg -n "def coareaJacobian|def tangentSpace|abbrev Rn" project/GMT/Ch02/Contract.lean`
- `rg -il coarea mathlib/Mathlib`
- `rg -n "coarea_chart_area_pullback|coarea_chart_fiber_disintegration" project mathlib/Mathlib lake-packages-25730c7c/simongmt/Poincare`
- `grep -n '^theorem\|^def\|^noncomputable def' mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `rg -n "theorem weighted_area_formula_volume_of_injective_derivative|theorem continuous_normDet|theorem areaJacobianAt_eq_normDet" lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/`
- `sed -n 540,580p mathlib/Mathlib/Analysis/Normed/Lp/ProdLp.lean; sed -n 180,215p mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `lean Explore.lean (#synth MeasureSpace/MeasurableSpace/BorelSpace/InnerProductSpace/FiniteDimensional on WithLp 2 (Rn m × Rn k); finrank = m + k; j b = toLp 2 (0,b) by rfl; L.normDet = L.toLinearMap.normDet by rfl)`
- `python3 -I gen.py (verifier gmt-compare.py child_modules/contract_scope + lean_contract.validate_lean_statement); lean NodeChallenge_00_coarea_chart_area_pullback.lean NodeChallenge_01_coarea_chart_fiber_disintegration.lean`
- `lean Assembly.lean (sorried stand-ins of both child types and frozen coarea_jacobian_linear_algebra; sorry-free check_parent : selected frozen type; #print axioms)`
- `lean ProofD.lean; lean ProofX.lean (#print axioms chart_area_pullback_check / chart_fiber_disintegration_check)`
- `python3 -I: lean_name reservation check over dag.json`
- `cmp project/GMT/Ch02/Contract.lean workspaces/gmt-ch02/GMT/Ch02/Contract.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Normed/Lp/ProdLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Normed/Lp/MeasurableSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaApproximation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-coarea-formula-a1-chart-coarea-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-coarea-formula-a1/decomposition-v1.json`
- `/tmp/chart-coarea-decomp-aGHPEL/check/Explore.lean`
- `/tmp/chart-coarea-decomp-aGHPEL/check/gen/NodeChallenge_00_coarea_chart_area_pullback.lean`
- `/tmp/chart-coarea-decomp-aGHPEL/check/gen/NodeChallenge_01_coarea_chart_fiber_disintegration.lean`
- `/tmp/chart-coarea-decomp-aGHPEL/check/Assembly.lean`
- `/tmp/chart-coarea-decomp-aGHPEL/agentD/ProofD.lean`
- `/tmp/chart-coarea-decomp-aGHPEL/agentX/ProofX.lean`

The pinned snapshot supplies every interface both children use, and no nonlinear co-area theorem exists to reuse. The snapshot's project/GMT/Ch02/Contract.lean is byte-identical to the workspace contract; it defines Rn (l.48), tangentSpace (l.86) and coareaJacobian (l.123).

Mathlib in the snapshot provides:
- WithLp.volume_preserving_toLp (Haar/InnerProductSpace.lean l.211), Measure.volume_eq_prod (Prod.lean l.177), lintegral_prod (l.1009) and Measurable.lintegral_prod_right' (l.123);
- MeasurePreserving.lintegral_comp (Lebesgue/Map.lean l.119), lintegral_indicator (Lebesgue/Basic.lean l.510) and setLIntegral_congr_fun (l.298);
- ContinuousOn.measurable_piecewise (BorelSpace/Basic.lean l.523), measurable_fderiv (FDeriv/Measurable.lean l.378) and WithLp.measurable_toLp (Normed/Lp/MeasurableSpace.lean l.33);
- WithLp.prodContinuousLinearEquiv (ProdLp.lean l.556) with prodContinuousLinearEquiv_symm_apply (l.562), and WithLp.fstL (l.567);
- hasFDerivAt_prodMk_right (FDeriv/Prod.lean l.80), HasFDerivAt.congr_of_eventuallyEq (FDeriv/Congr.lean l.176), HasFDerivAt.unique (FDeriv/Basic.lean l.174) and ContDiffOn.differentiableOn (ContDiff/Defs.lean l.578);
- finrank_euclideanSpace_fin (PiL2.lean l.205), ENNReal.ofReal_mul (Basic/ENNReal/Real.lean l.297) and InnerProductSpace.euclideanHausdorffMeasure_eq_volume (Euclidean/Volume/Measure.lean l.191).

The pinned SimonGMT package provides Chapter02.weighted_area_formula_volume_of_injective_derivative (WeightedArea.lean l.120; the target weight may be non-measurable), continuous_normDet (AreaApproximation.lean l.28) and areaJacobianAt_eq_normDet (Area.lean l.35).

No-match results:
- rg -il coarea finds no file under mathlib/Mathlib.
- Neither proposed name occurs in the project, Mathlib or SimonGMT.
- dag.json reserves neither name.

Lean checks:
- #synth on WithLp 2 (Rn m × Rn k) gives MeasureSpace = measureSpaceOfInnerProductSpace, plus WithLp.borelSpace and WithLp.instProdInnerProductSpace.
- Both statements validate, and the comparator-generated challenge modules compile.
- Assembly.lean proves the selected frozen type sorry-free from stand-ins of the two child types and the frozen coarea_jacobian_linear_algebra type.
- Complete proofs of the exact child types (ProofD.lean, ProofX.lean) compile with axioms only propext, Classical.choice and Quot.sound.

Reuse is therefore compatible and axiom-clean.
