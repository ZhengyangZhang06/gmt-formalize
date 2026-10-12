# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_open_dense-a1.density_of_approx_tangent-a1`
- Child DAG node: `root.regular_set_open_dense-a1.density_of_approx_tangent-a1.scaled_mult_integral_limit-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 3, Remark 1.8(2), with the matching lower bound from a cut-off equal to 1 on B_{1−ε}(0) and 0 off B_1(0). These are parent proof steps 1 and 3-6.
Setting: n ≥ 1, U open, V : RectifiableVarifold n ℓ U, M := V.carrier, θ := V.mult, Hⁿ := μHE[n], x ∈ U.
The hypothesis HasWeightedApproximateTangentSpaceAt n M θ x P means: finrank P = n, and for every f ∈ C_c(ℝ^{n+ℓ}, ℝ), I_r(f) := ∫_{η_{x,r}(M)} f(y)θ(x + r y) dHⁿ(y) → θ(x)·∫_P f dHⁿ along 𝓝[>]0.
Put ω := unitBallVolume n, t := θ(x), J(r) := r⁻ⁿ∫_{M ∩ B_r(x)} θ dHⁿ, ν_P := Hⁿ⌞P. Goal: J(r) → ωt along 𝓝[>]0.

1. Preliminaries. ω = π^{n/2}/Γ(n/2 + 1) > 0, because π^{n/2} > 0 and Γ(n/2 + 1) > 0. Since U is open and x ∈ U, there is e > 0 with open ball B̆_e(x) ⊆ U. Put d := e/4 > 0; then B_{2d}(x) = B_{e/2}(x) ⊆ B̆_e(x) ⊆ U.

2. Test functions. For ε > 0 let f_ε(y) := min(1, max(0, (1 + ε − ‖y‖)/ε)) and g_ε(y) := min(1, max(0, (1 − ‖y‖)/ε)). Both are continuous with values in [0, 1].
   - If ‖y‖ > 1 + ε, then (1 + ε − ‖y‖)/ε < 0, so f_ε(y) = 0. If ‖y‖ ≤ 1, then (1 + ε − ‖y‖)/ε ≥ 1, so f_ε(y) = 1.
   - If ‖y‖ > 1, then g_ε(y) = 0. If ‖y‖ ≤ 1 − ε, then (1 − ‖y‖)/ε ≥ 1, so g_ε(y) = 1.
   So f_ε vanishes off the compact ball B_{1+ε}(0) and g_ε off B_1(0). Both have compact support (HasCompactSupport.intro) and define elements of C_c(ℝ^{n+ℓ}, ℝ). In Lean write CompactlySupportedContinuousMap, since the C_c notation is not open in the contract scope.

3. Plane integrals. By the sibling theorem rsod_planeMeasure_closedBall, ν_P(B_s(0)) = ofReal(ωsⁿ) < ∞ for every s ≥ 0. Hence the indicator 1_{B_s(0)} is ν_P-integrable (integrable_indicator_iff, integrableOn_const) and ∫ 1_{B_s(0)} dν_P = ν_P(B_s(0)).toReal = ωsⁿ (integral_indicator_one).
   - Upper bound: 0 ≤ f_ε ≤ 1_{B_{1+ε}(0)} pointwise by step 2. So f_ε is ν_P-integrable (continuous and dominated, Integrable.mono'), and by integral_mono, ∫_P f_ε dHⁿ ≤ ω(1 + ε)ⁿ.
   - Lower bound: for 0 < ε < 1, 1_{B_{1−ε}(0)} ≤ g_ε ≤ 1_{B_1(0)} pointwise. So g_ε is ν_P-integrable and ∫_P g_ε dHⁿ ≥ ω(1 − ε)ⁿ > 0.

4. Comparisons. Let 0 < ε < 1 and 0 < r < d.
   (i) Apply the sibling theorem rsod_blowUp_integral_ballMass_bounds with φ := f_ε and R := 1 + ε ≥ 1. Its hypotheses hold: r(1 + ε) < 2d, so B_{r(1+ε)}(x) ⊆ B_{2d}(x) ⊆ U; f_ε is continuous, hence Borel; it takes values in [0, 1], vanishes off B_{1+ε}(0) and equals 1 on B_1(0). Part (b) gives J(r) ≤ I_r(f_ε).
   (ii) Apply it with φ := g_ε and R := 1. Here B_{r·1}(x) ⊆ B_{2d}(x) ⊆ U, and g_ε vanishes off B_1(0). Parts (a) and (c) give 0 ≤ I_r(g_ε) ≤ J(r).

5. t ≥ 0. Take ε = 1/2. By step 4(ii), I_r(g_{1/2}) ≥ 0 for every r ∈ (0, d), and (0, d) ∈ 𝓝[>]0. Since I_r(g_{1/2}) → t·∫_P g_{1/2} dHⁿ, the limit satisfies t·∫_P g_{1/2} dHⁿ ≥ 0 (ge_of_tendsto). As ∫_P g_{1/2} dHⁿ ≥ ω·2⁻ⁿ > 0 (step 3), we get t ≥ 0.

6. Lower bound. Let a < ωt.
   - The map ε ↦ tω(1 − ε)ⁿ is continuous with value tω > a at ε = 0. So there is ε ∈ (0, 1) with tω(1 − ε)ⁿ > a.
   - By steps 3 and 5, t·∫_P g_ε dHⁿ ≥ tω(1 − ε)ⁿ > a.
   - Since I_r(g_ε) → t·∫_P g_ε dHⁿ, eventually along 𝓝[>]0 we have I_r(g_ε) > a, and eventually r ∈ (0, d). For such r, J(r) ≥ I_r(g_ε) > a by step 4(ii).

7. Upper bound. Let b > ωt.
   - The map ε ↦ tω(1 + ε)ⁿ is continuous with value tω < b at ε = 0. So there is ε ∈ (0, 1) with tω(1 + ε)ⁿ < b.
   - By steps 3 and 5, t·∫_P f_ε dHⁿ ≤ tω(1 + ε)ⁿ < b.
   - Since I_r(f_ε) → t·∫_P f_ε dHⁿ, eventually I_r(f_ε) < b, and eventually r ∈ (0, d). For such r, J(r) ≤ I_r(f_ε) < b by step 4(i).

8. By steps 6 and 7, for every a < ωt and every b > ωt, eventually a < J(r) and eventually J(r) < b along 𝓝[>]0. By the characterization of limits in the order topology of ℝ (tendsto_order), J(r) → ωt = unitBallVolume n · θ(x). ∎

## Key steps

1. choose d > 0 with B_{2d}(x) ⊆ U; ω_n > 0
2. continuous compactly supported cut-offs f_ε, g_ε with g_ε ≤ 1_{B_1(0)} ≤ f_ε, f_ε = 1 on B_1, g_ε = 1 on B_{1−ε}
3. plane bounds ∫_P f_ε ≤ ω_n(1+ε)ⁿ and ∫_P g_ε ≥ ω_n(1−ε)ⁿ from sibling rsod_planeMeasure_closedBall
4. comparisons 0 ≤ I_r(g_ε) ≤ J(r) ≤ I_r(f_ε) for 0 < r < d from sibling rsod_blowUp_integral_ballMass_bounds
5. θ(x) ≥ 0 from the limit of I_r(g_{1/2}) ≥ 0
6. order-topology squeeze: choose ε by continuity at 0 for each a < ω_nθ(x) < b

## Reference use

### local-project

Queries:
- `diff -q <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Contract.lean (byte-identical) ; cat <snapshot>/manifest.json`
- `grep -n 'theorem\|lemma\|def \|notation' <snapshot>/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (μHE[d], Isometry.euclideanHausdorffMeasure_image, Isometry.map_euclideanHausdorffMeasure, euclideanHausdorffMeasure_homothety_image, InnerProductSpace.euclideanHausdorffMeasure_eq_volume)`
- `grep -rn volume_closedBall <snapshot>/mathlib/Mathlib --include=*.lean | grep -E 'theorem|lemma' ; sed -n 330,365p <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `grep -rn -E '^(theorem|lemma) (integral_smul_measure|MeasurableEmbedding.integral_map|setIntegral_indicator|integral_mono_ae|ofReal_integral_eq_lintegral_ofReal|withDensity_apply|restrict_restrict|ae_restrict_mem₀|integrable_indicator_iff|integral_indicator_one|tendsto_order|nonneg_of_mul_nonneg_left) ' <snapshot>/mathlib/Mathlib`
- `grep -n 'def \|theorem \|lemma ' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean ; sed -n 1,365p of it (blowUpMap, HasWeightedApproximateTangentSpaceAt, .unique)`
- `sed -n 1,260p .lake/packages/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean (hausdorff_blowUp_image, blowUp_image_inter_closedBall, planeMeasure_unit_closedBall, tangentDensityCutoff, integral_blowUp_le_scaled_weight, one_le_density_of_approximateTangent)`
- `grep -n -E '^(open|namespace|section|noncomputable section|end|universe|set_option|variable|attribute|local)' GMT/Ch05/Contract.lean (comparator child scope) ; sed -n 520,600p verifier/gmt-compare.py (child_modules)`
- `sed -n 240,345p book/chapter-03.txt (Definition 1.7, Remark 1.8(2), Theorem 1.9)`
- `grep -x <name> over all lean_name values in dag.json and nodes/*/*.json (110 reserved) ; grep -rlE over .swarm-worktrees/*/gmt-ch05/GMT/Ch05 (21 worktrees) and lake-packages simongmt/Poincare for the 5 proposed names`
- `lake env lean /tmp/dat-work/proj/Dat/{Stmts,Glue,CoreD,Leaves,Full,FullCmp}.lean ; python3 -I verifier/lean_contract.py validate_lean_statement on the 6 statements`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Topology/Order/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/comparator/README.md`
- `/tmp/dat-work/proj/Dat/Full.lean`
- `/tmp/dat-work/proj/Dat/FullCmp.lean`

Snapshot pins project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d. The snapshot Contract.lean is byte-identical to the workspace contract.

No-match results:
- No Mathlib or simongmt declaration states any of the five children for the Ch05 RectifiableVarifold. That structure (weight = (μHE[n]⌞M).withDensity(ofReal ∘ θ)) appears only in GMT/Ch05.
- simongmt Chapter04/TangentDensity.lean proves the one-sided, unweighted analogue `one_le_density_of_approximateTangent` for the excluded Chapter04.RectifiableVarifold, plus generic helpers: `hausdorff_blowUp_image`, `planeMeasure_unit_closedBall` (in terms of Chapter01.realUnitBallVolume) and `tangentDensityCutoff`.
- Those helpers are not imported by the Submission, which imports only Chapter03.Rectifiable. The children therefore re-derive them directly from Mathlib.

Mathlib lemmas used (snapshot paths, with line numbers):
- Geometry/Euclidean/Volume/Measure.lean: Isometry.euclideanHausdorffMeasure_image (l.131), Isometry.map_euclideanHausdorffMeasure (l.141), euclideanHausdorffMeasure_homothety_image (l.164), InnerProductSpace.euclideanHausdorffMeasure_eq_volume (l.191).
- Lebesgue/VolumeOfBalls.lean: InnerProductSpace.volume_closedBall (l.354; needs an extra import in the Submission, which the comparator permits).
- Bochner/Basic.lean: integral_smul_measure (l.1052), MeasurableEmbedding.integral_map (l.1093), integral_mono_ae (l.664), ofReal_integral_eq_lintegral_ofReal (l.739).
- Bochner/Set.lean: setIntegral_indicator (l.194), integral_indicator_one (l.533).
- Measure/Restrict.lean: restrict_restrict (l.205), ae_restrict_mem₀ (l.637).
- WithDensity.lean: withDensity_apply (l.44).
- IntegrableOn.lean: integrable_indicator_iff (l.340).
- Topology/Order/Basic.lean: tendsto_order (l.139).

simongmt Chapter03 gives blowUpMap x r y = r⁻¹ • (y - x), which unfolds by rfl from the Submission, and the exact HasWeightedApproximateTangentSpaceAt used in the frozen type.

The five names (rsod_blowUp_setIntegral_eq, rsod_planeMeasure_closedBall, rsod_weight_closedBall_eq_ofReal_integral, rsod_blowUp_integral_ballMass_bounds, rsod_tendsto_scaled_mult_integral) are unused anywhere in the run, the worktrees and simongmt.

Lean check: all statements elaborate in the comparator scope and pass validate_lean_statement. Full proofs of every child and of the parent assembly compile (Dat/Full.lean) with axioms [propext, Classical.choice, Quot.sound]. The simulated comparator targets `exact Submission.X` succeed (Dat/FullCmp.lean).
