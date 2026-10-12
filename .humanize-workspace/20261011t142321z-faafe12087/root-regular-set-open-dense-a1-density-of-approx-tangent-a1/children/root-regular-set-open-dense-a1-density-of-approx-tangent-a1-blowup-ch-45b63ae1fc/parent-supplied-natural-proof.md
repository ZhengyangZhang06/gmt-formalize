# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_open_dense-a1.density_of_approx_tangent-a1`
- Child DAG node: `root.regular_set_open_dense-a1.density_of_approx_tangent-a1.blowup_change_of_variables-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 2 (change of variables), in an unconditional form.
Setting: n, ℓ ∈ ℕ; M ⊆ ℝ^{n+ℓ} arbitrary; f, θ : ℝ^{n+ℓ} → ℝ arbitrary; x ∈ ℝ^{n+ℓ}; r > 0; Hⁿ := μHE[n]; η := η_{x,r}, η(z) = r⁻¹(z − x). All integrals are Bochner integrals. No integrability is assumed and none is needed.

1. η is a homeomorphism of ℝ^{n+ℓ}. It is the translation z ↦ z − x followed by the dilation w ↦ r⁻¹w (r⁻¹ ≠ 0), with continuous inverse y ↦ x + r y. Hence η is a bijection and a Borel measurable equivalence, in particular a measurable embedding.
   Lean: e := (Homeomorph.subRight x).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne')). This is definitionally Chapter03.blowUpMap x r (`fun z => rfl`). Take E := e.toMeasurableEquiv.

2. Scaling. For every set S ⊆ ℝ^{n+ℓ}, measurable or not, Hⁿ(η(S)) = (r⁻¹)ⁿ·Hⁿ(S).
   - η(S) = h(τ(S)), where τ(y) = y − x and h is the homothety with centre 0 and ratio r⁻¹.
   - τ is an isometry: dist(a − x, b − x) = ‖a − b‖. So Hⁿ(τ(S)) = Hⁿ(S) by Isometry.euclideanHausdorffMeasure_image.
   - Images under h have μHE[n]-measure multiplied by ‖r⁻¹‖₊ⁿ (euclideanHausdorffMeasure_homothety_image), and ‖r⁻¹‖ = r⁻¹ because r > 0.
   In [0,∞] the factor is c := ofReal(r⁻¹)ⁿ, which is finite and positive.

3. Restricted measures. Claim: Hⁿ⌞η(M) = c·η_#(Hⁿ⌞M). It suffices to compare the two measures on Borel sets A (Measure.ext).
   - Since η is a bijection, A ∩ η(M) = η(η⁻¹(A) ∩ M) (Set.image_inter and Set.image_preimage_eq).
   - Hence (Hⁿ⌞η(M))(A) = Hⁿ(A ∩ η(M)) = Hⁿ(η(η⁻¹(A) ∩ M)) = c·Hⁿ(η⁻¹(A) ∩ M), by step 2.
   - Since η⁻¹(A) is Borel, Hⁿ(η⁻¹(A) ∩ M) = (Hⁿ⌞M)(η⁻¹(A)) = (η_#(Hⁿ⌞M))(A) (Measure.restrict_apply, Measure.map_apply).
   Measure.restrict_apply only requires the evaluated set to be measurable, never the restricting set, so measurability of M is not used.

4. Put g(y) := f(y)·θ(x + r y).
   - By step 3 and the scalar rule ∫ g d(c·μ) = c.toReal·∫ g dμ (integral_smul_measure, valid for every g): ∫_{η(M)} g dHⁿ = c.toReal·∫ g d(η_#(Hⁿ⌞M)).
   - By the change of variables for a measurable embedding (MeasurableEmbedding.integral_map, valid for every g, integrable or not): ∫ g d(η_#(Hⁿ⌞M)) = ∫_M g(η(z)) dHⁿ(z).
   - Finally c.toReal = (r⁻¹)ⁿ = (rⁿ)⁻¹ (ENNReal.toReal_pow, ENNReal.toReal_ofReal, inv_pow).

5. For every z, x + r·η(z) = x + r·(r⁻¹(z − x)) = x + (z − x) = z, because r·r⁻¹ = 1. Thus g(η(z)) = f(η(z))·θ(z) for all z.

Combining steps 4 and 5: ∫_{η(M)} f(y)·θ(x + r y) dHⁿ(y) = (rⁿ)⁻¹·∫_M f(η(z))·θ(z) dHⁿ(z). ∎

## Key steps

1. η_{x,r} is a homeomorphism, hence a bijective measurable embedding
2. Hⁿ(η(S)) = (r⁻¹)ⁿ Hⁿ(S) for every set S (translation isometry + homothety scaling)
3. Hⁿ⌞η(M) = ofReal(r⁻¹)ⁿ · η_#(Hⁿ⌞M), checked on Borel A via A ∩ η(M) = η(η⁻¹A ∩ M)
4. integral_smul_measure and MeasurableEmbedding.integral_map, both valid without integrability
5. simplify x + r·η(z) = z

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
