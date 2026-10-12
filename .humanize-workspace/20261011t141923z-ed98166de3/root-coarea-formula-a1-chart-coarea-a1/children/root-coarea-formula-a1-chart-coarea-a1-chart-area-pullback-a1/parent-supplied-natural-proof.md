# Parent-supplied natural-language proof

- Parent DAG node: `root.coarea_formula-a1.chart_coarea-a1`
- Child DAG node: `root.coarea_formula-a1.chart_coarea-a1.chart_area_pullback-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 1 (chain-rule part), 2 and 3 of the selected node's supplied proof, specialized so that the linear-algebra input enters through the hypothesis hLA. hLA is the (N,m,k,M,f)-instance of the second conjunct of the frozen sibling coarea_jacobian_linear_algebra.

Notation.
- P := WithLp 2 (ℝᵐ × ℝᵏ) carries its Euclidean inner product and volume dp (Mathlib's inner-product-space volume).
- j : ℝᵏ → P is the continuous linear map (WithLp.prodContinuousLinearEquiv 2 ℝ ℝᵐ ℝᵏ).symm ∘L inr. The identity j(b) = toLp(0,b) holds definitionally.
- For a continuous linear map L, normDet(L) := LinearMap.normDet L ≥ 0. For a CLM, L.normDet and L.toLinearMap.normDet are the same term.
- S′ := Ω ∩ Ψ⁻¹(S).
- J*f := coareaJacobian M f. It is a real square root, so J*f(x) ≥ 0 for every x.
- J(p) := normDet(DΨ(p)). This is SimonGMT's areaJacobianAt Ψ p by definition (Chapter02.areaJacobianAt_eq_normDet).
- J_v(p) := normDet(DΨ(p)∘j).
- hLA denotes the last hypothesis.

1. Differentiability. Let p ∈ Ω. Ψ is C¹ on Ω and 1 ≠ 0, so Ψ is differentiable within Ω at p (ContDiffOn.differentiableOn). Ω is open, hence a neighbourhood of p, so Ψ is differentiable at p. In particular Ψ is continuous on Ω.

2. S′ is Borel. Let Ψ̃ := Ω.piecewise Ψ (fun _ ↦ 0), using classical decidability. Ψ is continuous on Ω, the constant is continuous on Ωᶜ, and Ω is open, hence Borel. So Ψ̃ is Borel measurable by ContinuousOn.measurable_piecewise. Since Ψ̃ = Ψ on Ω, we have S′ = Ω ∩ Ψ̃⁻¹(S), an intersection of two Borel sets.

3. Ψ(S′) = S. If p ∈ S′, then Ψ(p) ∈ S. Conversely, let x ∈ S. Since S ⊆ Ψ(Ω), there is p ∈ Ω with Ψ(p) = x, and p ∈ S′ because Ψ(p) ∈ S.

4. finrank_ℝ P = m + k. P is linearly isomorphic to ℝᵐ × ℝᵏ via WithLp.linearEquiv, and finrank(ℝᵐ × ℝᵏ) = m + k.

5. Area formula on P. Apply SimonGMT Chapter02.weighted_area_formula_volume_of_injective_derivative with E := P, F := ℝᴺ, s := S′, the map Ψ, and the weight w(x) := g(x)·ofReal(J*f(x)). This weight need not be measurable. The hypotheses hold:
- S′ is Borel (2).
- Ψ is differentiable at every p ∈ S′ ⊆ Ω (1).
- DΨ(p) is injective for p ∈ S′ ⊆ Ω (hypothesis).
- Ψ is injective on S′ ⊆ Ω (InjOn.mono).
The lemma gives ∫_{Ψ(S′)} w dμHE[finrank P] = ∫_{S′} ofReal(J(p))·w(Ψ p) dp. Rewriting with Ψ(S′) = S (3) and finrank P = m + k (4):
∫_S g·ofReal(J*f) dμHE[m+k] = ∫_{S′} ofReal(J(p))·(g(Ψ p)·ofReal(J*f(Ψ p))) dp.

6. Chain rule. Fix p ∈ Ω. Let π₁ := WithLp.fstL 2 ℝ ℝᵐ ℝᵏ, the continuous linear map q ↦ WithLp.fst q =: q₁.
- Ω is a neighbourhood of p and f(Ψ q) = q₁ for every q ∈ Ω. So f∘Ψ and π₁ agree on a neighbourhood of p.
- π₁ is its own derivative everywhere. Hence f∘Ψ has Fréchet derivative π₁ at p (HasFDerivAt.congr_of_eventuallyEq).
- f is differentiable at Ψ(p) by hypothesis, and Ψ is differentiable at p by 1. By the chain rule, f∘Ψ also has derivative Df(Ψ p)∘DΨ(p) at p.
- By uniqueness of the Fréchet derivative (HasFDerivAt.unique), Df(Ψ p)∘DΨ(p) = π₁. That is, Df(Ψ p)(DΨ(p) q) = q₁ for every q ∈ P.

7. Pointwise Jacobian identity. Fix p ∈ Ω and apply hLA with x := Ψ(p), A := DΨ(p) and B := DΨ(p)∘j. Its premises hold:
- A is injective (hypothesis).
- tangentSpace M (Ψ p) = range A (hypothesis).
- Df(x)(A q) = q₁ for all q ∈ P (6).
- B b = A(j b) = A(toLp(0,b)) for all b ∈ ℝᵏ (definition of j).
Hence J*f(Ψ p)·J(p) = J_v(p).

8. The integrands agree on S′. Let p ∈ S′ ⊆ Ω. In [0,∞] we use commutativity and associativity, then ENNReal.ofReal_mul (valid because J*f(Ψ p) ≥ 0), then 7:
ofReal(J(p))·(g(Ψ p)·ofReal(J*f(Ψ p)))
= g(Ψ p)·(ofReal(J*f(Ψ p))·ofReal(J(p)))
= g(Ψ p)·ofReal(J*f(Ψ p)·J(p))
= g(Ψ p)·ofReal(J_v(p))
= ofReal(J_v(p))·g(Ψ p).

9. Conclusion. S′ is Borel and the two integrands agree on S′ (8). So their integrals over S′ agree (setLIntegral_congr_fun). Together with 5:
∫_S g·ofReal(coareaJacobian M f) dμHE[m+k] = ∫_{Ω∩Ψ⁻¹(S)} ofReal(normDet(DΨ(p)∘j))·g(Ψ p) dp.
This is the claim.

## Key steps

1. Ψ is differentiable at every point of the open set Ω. S′ := Ω∩Ψ⁻¹(S) is Borel, via the measurable piecewise extension Ω.piecewise Ψ 0. Ψ(S′) = S because S ⊆ Ψ(Ω), and finrank P = m+k.
2. The SimonGMT weighted area formula for Ψ on S′ with the weight g·ofReal(J*f), which need not be measurable, gives ∫_S g·ofReal(J*f) dμHE[m+k] = ∫_{S′} ofReal(normDet DΨ(p))·g(Ψp)·ofReal(J*f(Ψp)) dp.
3. Chain rule plus uniqueness of the derivative: f∘Ψ = fst near each p ∈ Ω, so Df(Ψp)(DΨ(p)q) = q₁ for all q.
4. hLA with x = Ψp, A = DΨ(p) and B = DΨ(p)∘j (B b = A(toLp(0,b)) by definition) gives J*f(Ψp)·normDet DΨ(p) = normDet(DΨ(p)∘j).
5. ENNReal.ofReal_mul (J*f ≥ 0) turns the integrand on S′ into ofReal(normDet(DΨ(p)∘j))·g(Ψp), and setLIntegral_congr_fun concludes.

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
