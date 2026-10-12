# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_open_dense-a1.density_of_approx_tangent-a1`
- Child DAG node: `root.regular_set_open_dense-a1.density_of_approx_tangent-a1.weight_ball_integral-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 2, last sentence (μ(B_r(x)) = ∫⁻_{M ∩ B_r(x)} ofReal θ dHⁿ = ofReal(∫_{M ∩ B_r(x)} θ dHⁿ)).
Setting: n, ℓ ∈ ℕ, U ⊆ ℝ^{n+ℓ}, V : RectifiableVarifold n ℓ U with carrier M and multiplicity θ, Hⁿ := μHE[n]. By definition μ_V := V.weight = (Hⁿ⌞M).withDensity(z ↦ ofReal(θ z)). Let x ∈ ℝ^{n+ℓ}, r ∈ ℝ, and B := B_r(x) (closed ball) ⊆ U.

1. B is closed and bounded in the finite-dimensional space ℝ^{n+ℓ}, hence compact (isCompact_closedBall), and B ⊆ U. By the structure field integrableOn_mult, θ is Hⁿ-integrable on M ∩ B.

2. B is Borel. By the definition of withDensity (withDensity_apply), μ_V(B) = ∫⁻_B ofReal(θ) d(Hⁿ⌞M).
   By Measure.restrict_restrict (B measurable), (Hⁿ⌞M)⌞B = Hⁿ⌞(B ∩ M). Since B ∩ M = M ∩ B, μ_V(B) = ∫⁻_{M ∩ B} ofReal(θ) dHⁿ.

3. θ ≥ 0 almost everywhere for Hⁿ⌞(M ∩ B).
   - M is Hⁿ-null-measurable (field nullMeasurableSet_carrier) and B is Borel, so M ∩ B is Hⁿ-null-measurable.
   - Hence Hⁿ⌞(M ∩ B)-almost every point lies in M ∩ B (ae_restrict_mem₀).
   - At such a point z ∈ M we have θ(z) > 0 (field mult_pos).

4. For a function that is integrable and almost everywhere nonnegative for a measure, ofReal of its integral equals the lower integral of ofReal of it (ofReal_integral_eq_lintegral_ofReal). Apply this to θ and Hⁿ⌞(M ∩ B) using steps 1 and 3: ofReal(∫_{M ∩ B} θ dHⁿ) = ∫⁻_{M ∩ B} ofReal(θ) dHⁿ.
   With step 2: μ_V(B_r(x)) = ofReal(∫_{M ∩ B_r(x)} θ dHⁿ). ∎

## Key steps

1. closed ball compact and ⊆ U ⇒ θ integrable on M ∩ B_r(x) (integrableOn_mult)
2. withDensity_apply + Measure.restrict_restrict ⇒ μ_V(B) = ∫⁻_{M∩B} ofReal θ dHⁿ
3. θ ≥ 0 a.e. on M ∩ B (null-measurable carrier, ae_restrict_mem₀, mult_pos)
4. ofReal_integral_eq_lintegral_ofReal

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
