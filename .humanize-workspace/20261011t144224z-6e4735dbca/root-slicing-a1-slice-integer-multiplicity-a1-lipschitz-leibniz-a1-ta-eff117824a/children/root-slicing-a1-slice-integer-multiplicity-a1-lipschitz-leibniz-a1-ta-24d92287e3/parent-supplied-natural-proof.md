# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.tangential_weak_limit-a1.chart_integral_eq-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.tangential_weak_limit-a1.chart_integral_eq-a1.weighted_transfer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 3–6 of the parent proof of chart_integral_eq, with the chart data abstracted: μ plays Lⁿ⌞D, ν plays Hⁿ⌞A, J plays JΦ, and the hypothesis plays the nonnegative change of variables of step 1. μ need not be σ-finite because the null-measurable versions of the withDensity lemmas are used. Notation: ofReal = ENNReal.ofReal : ℝ → [0, ∞]; 1_S is the indicator function of S with value 1 on S; Φ_#ρ = Measure.map Φ ρ.
1. (The density.) Put f(x) := (J(x)).toNNReal ∈ [0, ∞). J is μ-a.e. measurable and r ↦ r.toNNReal is measurable, so f is μ-a.e. measurable (`AEMeasurable.real_toNNReal`). For every x, the coercion of f(x) into [0, ∞] equals ofReal(J(x)), which is the definition of ENNReal.ofReal. Because J(x) ≥ 0, the coercion of f(x) into ℝ equals J(x) (`Real.coe_toNNReal`).
2. (The weighted measure.) Let ρ := μ.withDensity (x ↦ (f(x) : [0, ∞])), the measure with density ofReal∘J with respect to μ. Then ρ ≪ μ (`withDensity_absolutelyContinuous`), so the μ-a.e. measurable map Φ is also ρ-a.e. measurable (`AEMeasurable.mono_ac`).
3. (Φ pushes ρ forward to ν.) Let S ⊆ Y be measurable. Since Φ is μ-a.e. measurable, Φ⁻¹(S) is μ-null-measurable (`AEMeasurable.nullMeasurableSet_preimage`). Then
(Φ_#ρ)(S) = ρ(Φ⁻¹(S)) (`Measure.map_apply_of_aemeasurable`, using that Φ is ρ-a.e. measurable by step 2)
= ∫⁻_{Φ⁻¹(S)} ofReal(J(x)) dμ(x) (`withDensity_apply₀`, Φ⁻¹(S) being μ-null-measurable)
= ∫⁻ 1_{Φ⁻¹(S)}(x)·ofReal(J(x)) dμ(x) (`lintegral_indicator₀`)
= ∫⁻ 1_S(Φ(x))·ofReal(J(x)) dμ(x) (pointwise: if Φ(x) ∈ S, then x ∈ Φ⁻¹(S) and both integrands equal ofReal(J(x)); if Φ(x) ∉ S, both integrands are 0)
= ∫⁻ 1_S dν (the hypothesis with g = 1_S, which is measurable because S is)
= ν(S) (`lintegral_indicator_one`).
Two measures on Y that agree on every measurable set are equal (`Measure.ext`), so Φ_#ρ = ν.
4. (Transfer along Φ.) Let F : Y → E be ν-integrable. By step 3, F is Φ_#ρ-integrable, and in particular Φ_#ρ-a.e. strongly measurable. Since Φ is ρ-a.e. measurable (step 2), `integrable_map_measure` shows that x ↦ F(Φ(x)) is ρ-integrable. `integral_map` together with step 3 gives ∫ F dν = ∫ F d(Φ_#ρ) = ∫ F(Φ(x)) dρ(x).
5. (Removing the density.) Since f is μ-a.e. measurable (step 1), `integrable_withDensity_iff_integrable_smul₀` turns the ρ-integrability of x ↦ F(Φ(x)) into the μ-integrability of x ↦ f(x)•F(Φ(x)). `integral_withDensity_eq_integral_smul₀` gives ∫ F(Φ(x)) dρ(x) = ∫ f(x)•F(Φ(x)) dμ(x).
6. (Identification of the weight.) For every x and every v ∈ E, f(x)•v = (f(x) : ℝ)•v = J(x)•v (`NNReal.smul_def` and step 1). So the function x ↦ f(x)•F(Φ(x)) is x ↦ J(x)•F(Φ(x)). By step 5 it is μ-integrable, and by steps 4–5, ∫ F dν = ∫ F(Φ(x)) dρ(x) = ∫ J(x)•F(Φ(x)) dμ(x). ∎

## Key steps

1. f := J.toNNReal is μ-a.e. measurable; its coercion to [0, ∞] is ofReal∘J and its coercion to ℝ is J, because J ≥ 0.
2. ρ := μ.withDensity f satisfies ρ ≪ μ, so Φ is ρ-a.e. measurable.
3. Φ_#ρ = ν: for measurable S, chain map_apply_of_aemeasurable, withDensity_apply₀ (Φ⁻¹S is μ-null-measurable), lintegral_indicator₀, the pointwise identity 1_{Φ⁻¹S}·ofReal J = (1_S∘Φ)·ofReal J, the hypothesis with g = 1_S, and lintegral_indicator_one; conclude by Measure.ext.
4. integrable_map_measure and integral_map: F∘Φ is ρ-integrable and ∫ F dν = ∫ F∘Φ dρ.
5. integrable_withDensity_iff_integrable_smul₀ and integral_withDensity_eq_integral_smul₀ remove the density; f(x)•v = J(x)•v by NNReal.smul_def and Real.coe_toNNReal.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `diff project/GMT/Ch06/Contract.lean <(git show HEAD:GMT/Ch06/Contract.lean) (identical); git show 92b42a6dbf98c7a1b88c4b032d67632f248b6a4c:GMT/Ch06/Submission.lean (proof base = bare contract, 364 lines)`
- `grep -rn 'theorem measurable_fderiv\b|theorem measurable_fderiv |instance.*measurableSpace.*→L|ContinuousLinearMap.measurableSpace|ContinuousLinearMap.borelSpace' mathlib/Mathlib; grep -rn 'measurableSpace\b.*:=\s*borel|MeasurableSpace (.*→L\[' mathlib/Mathlib`
- `grep -rn -A3 'theorem integral_withDensity_eq_integral_smul\b|theorem integrable_withDensity_iff_integrable_smul\b|theorem withDensity_apply'|theorem withDensity_apply₀|theorem integral_map |theorem integrable_map_measure|theorem map_apply_of_aemeasurable|theorem lintegral_indicator₀|theorem withDensity_absolutelyContinuous\b|theorem integrable_withDensity_iff_integrable_smul₀|theorem integral_withDensity_eq_integral_smul₀' mathlib/Mathlib`
- `rg -n 'theorem (integral_map_withDensity|map_withDensity|integral_withDensity_map|withDensity_map)' mathlib/Mathlib`
- `python3 scan of dag.json (622 nodes): regex gram|jacobian|withDensity|integral_map|Bochner|lintegral|measurable_fderiv|Real.sqrt (Matrix over title/statement/lean_statement, and 'Measurable (fun … => Real.sqrt' / 'Measurable (fun … fderiv' / withDensity / Measure.map+Integrable over lean_statement; exact types of lpf_raf_chart_change_of_variables, lpf_pi_signed_fibre_sum, lpf_wtc_caf_signed_of_lintegral, lpf_wtc_cat_gram_jacobian_continuous, slicing_im_si_signed_coarea, lpf_raf_chart_area_formula, lpf_raf_local_lipschitz_area, slicing_im_ll_twl_coefficient_field`
- `git show 9fc44225b304fca8af9dead3256575ef03818d1e -- GMT/Ch06/Submission.lean (accepted lpf_raf_chart_change_of_variables candidate and its exact type)`
- `read verifier/gmt-compare.py contract_scope/child_modules (challenge = import GMT.Ch06.Submission + replayed namespace GMT.Ch06 scope; solution = exact Submission.X)`
- `collision check: python3 over dag.json lean_name for slicing_im_ll_twl_cie_weighted_transfer / slicing_im_ll_twl_cie_jacobian_measurable / slicing_im_ll_twl_cie; rg -l 'slicing_im_ll_twl_cie|weighted_transfer|jacobian_measurable' over the snapshot project and lake-packages-25730c7c/simongmt (no match)`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/toolchains/lean-4.35.0-rc3-linux/bin/lake env lean /tmp/cie_split/check/Avail.lean (#check of measurable_fderiv, the ₀ withDensity lemmas, withDensity_apply₀, integral_map, integrable_map_measure, Measure.map_apply_of_aemeasurable, lintegral_indicator₀, withDensity_absolutelyContinuous, ContinuousOn.aemeasurable, Continuous.matrix_det in comparator scope)`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/toolchains/lean-4.35.0-rc3-linux/bin/lake env lean /tmp/cie_split/check/Children.lean and /tmp/cie_split/check/Assembly.lean (children proved; parent assembled)`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/toolchains/lean-4.35.0-rc3-linux/bin/lake env lean /tmp/cie_split/final/ChallengeA.lean, ChallengeB.lean (exit 0) and /tmp/cie_split/final/Integrated.lean (exit 0; child axioms propext, Classical.choice, Quot.sound; parent non-standard axiom only from the ccv stand-in; NodeSolution exact checks for both children and the parent)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-ta-eff117824a/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-ta-eff117824a/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-ta-eff117824a/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/cie_split/check/Avail.lean`
- `/tmp/cie_split/check/Children.lean`
- `/tmp/cie_split/check/Assembly.lean`
- `/tmp/cie_split/final/ChallengeA.lean`
- `/tmp/cie_split/final/ChallengeB.lean`
- `/tmp/cie_split/final/Integrated.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) has a GMT/Ch06/Contract.lean byte-identical to the frozen contract. The proof base's Submission.lean is the bare contract, so children may use only contract, SimonGMT and Mathlib names. Every Mathlib fact the split needs is in the import closure: measurable_fderiv (Analysis/Calculus/FDeriv/Measurable.lean:378) with the global Borel instance ContinuousLinearMap.instMeasurableSpace (Constructions/BorelSpace/ContinuousLinearMap.lean:47); withDensity_apply₀ (null-measurable sets, no s-finiteness) and withDensity_absolutelyContinuous (Measure/WithDensity.lean); integrable_withDensity_iff_integrable_smul₀ and integrable_map_measure (Function/L1Space/Integrable.lean); integral_withDensity_eq_integral_smul₀ (Integral/Bochner/ContinuousLinearMap.lean:296); integral_map (Integral/Bochner/Basic.lean:1081); Measure.map_apply_of_aemeasurable (Measure/Map.lean:166); lintegral_indicator₀ (Integral/Lebesgue/Basic.lean:518). Neither child exists in Mathlib or the DAG. The only map_withDensity result is the equidimensional map_withDensity_abs_det_fderiv_eq_addHaar (Function/Jacobian.lean:1127), which does not apply to ℝⁿ → ℝ^P with Hausdorff measure. The DAG's Jacobian lemma lpf_wtc_cat_gram_jacobian_continuous needs ContDiff ℝ 1. The accepted sibling lpf_raf_chart_change_of_variables (candidate 9fc44225) has exactly the type the parent assembly needs, and its third conjunct matches the transfer lemma's hypothesis verbatim under ν = Hⁿ⌞A, μ = Lⁿ⌞D. Scratch Lean in the exact comparator scope proves both children (standard axioms only) and proves the parent's byte-identical frozen type from them. The proposed names occur nowhere in the DAG, the snapshot or SimonGMT.
