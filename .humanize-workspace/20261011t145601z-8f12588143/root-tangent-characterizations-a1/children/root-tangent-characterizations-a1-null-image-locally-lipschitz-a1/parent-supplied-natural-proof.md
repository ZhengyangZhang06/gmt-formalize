# Parent-supplied natural-language proof

- Parent DAG node: `root.tangent_characterizations-a1`
- Child DAG node: `root.tangent_characterizations-a1.null_image_locally_lipschitz-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: fact (F2) in the Notation section of the parent proof: 'cover the open set by countably many sets on which the map is Lipschitz; SimonGMT euclideanHausdorffMeasure_image_le_of_lipschitzOn'. This is the null-set part of Simon Ch. 2, Theorem 1.8(i), as used for chart images in Ch. 3, Remark 1.3 and in the proof of Theorem 1.6 '⇒' (chapter-03.txt lines 113-143).

Setting. Fix V, ψ and Z as in the statement. LocallyLipschitzOn V ψ means: for every u ∈ V there are K_u ≥ 0 and t_u ∈ 𝓝[V] u such that ψ is K_u-Lipschitz on t_u.

1. Fix u ∈ V. Since V is open and u ∈ V, 𝓝[V] u = 𝓝 u (IsOpen.nhdsWithin_eq). So t_u is a neighbourhood of u and contains an open set O_u with u ∈ O_u (mem_nhds_iff). ψ is K_u-Lipschitz on O_u ⊆ t_u (LipschitzOnWith.mono).

2. The sets O_u (u ∈ V) are open and ℝⁿ is second countable. By Lindelöf (Mathlib TopologicalSpace.isOpen_biUnion_countable) there is a countable T ⊆ V with ⋃_{u∈T} O_u = ⋃_{u∈V} O_u. Every z ∈ V lies in O_z, so V ⊆ ⋃_{u∈T} O_u. As Z ⊆ V, we get Z ⊆ ⋃_{u∈T} (Z ∩ O_u), and therefore ψ(Z) ⊆ ⋃_{u∈T} ψ(Z ∩ O_u) (image_iUnion₂).

3. Fix u ∈ T. ψ is K_u-Lipschitz on Z ∩ O_u ⊆ O_u, so Hⁿ(ψ(Z ∩ O_u)) ≤ K_uⁿ·Hⁿ(Z ∩ O_u). This is the Lipschitz image estimate for the Hausdorff (outer) measure of arbitrary sets, in the μHE normalisation: SimonGMT Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn, derived from Mathlib LipschitzOnWith.hausdorffMeasure_image_le.

4. On ℝⁿ = EuclideanSpace ℝ (Fin n), μHE[n] equals Lebesgue measure (Mathlib EuclideanSpace.euclideanHausdorffMeasure_eq_volume). Hence Hⁿ(Z ∩ O_u) = Lⁿ(Z ∩ O_u) ≤ Lⁿ(Z) = 0. By Step 3, Hⁿ(ψ(Z ∩ O_u)) ≤ K_uⁿ·0 = 0.

5. T is countable, so countable subadditivity (measure_biUnion_null_iff) gives Hⁿ(⋃_{u∈T} ψ(Z ∩ O_u)) = 0. By Step 2 and monotonicity, Hⁿ(ψ(Z)) = 0. ∎

## Key steps

1. Since V is open, each u ∈ V has an open O_u ∋ u on which ψ is K_u-Lipschitz.
2. Lindelöf: a countable T ⊆ V with V ⊆ ⋃_{u∈T} O_u, so ψ(Z) ⊆ ⋃_{u∈T} ψ(Z ∩ O_u).
3. Hⁿ(ψ(Z ∩ O_u)) ≤ K_uⁿ Hⁿ(Z ∩ O_u) = K_uⁿ Lⁿ(Z ∩ O_u) = 0, using μHE[n] = volume on ℝⁿ.
4. Countable subadditivity gives Hⁿ(ψ(Z)) = 0.

## Reference use

### local-project

Queries:
- `grep -n "def blowUpMap|def CountablyRectifiable|def HasApproximateTangentSpaceAt|def HasWeightedApproximateTangentSpaceAt|def PurelyUnrectifiable" -A 14 simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -rn "blowUpMap" simongmt/Poincare/SimonGMT --include=*.lean`
- `grep -rn "theorem.*euclideanHausdorffMeasure.*smul|theorem euclideanHausdorffMeasure_image|theorem.*image_le_of_lipschitzOn|theorem.*image_null|theorem.*image_eq_zero" simongmt/Poincare/SimonGMT`
- `grep -rn "theorem|lemma" mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `grep -rn "ContDiffAt.exists_lipschitzOnWith|ContDiffOn.locallyLipschitzOn|isOpen_iUnion_countable|isOpen_biUnion_countable|integral_withDensity_eq_integral_toReal_smul|withDensity_apply_eq_zero" mathlib/Mathlib`
- `grep -rn "Integrable.lintegral_lt_top|restrict_apply₀'|ae_restrict_mem₀|measure_biUnion_null_iff|image_iUnion₂|ae_restrict_iff'₀" mathlib/Mathlib`
- `grep -rn "LocallyLipschitzOn.*hausdorff|hausdorffMeasure.*LocallyLipschitz" mathlib/Mathlib simongmt/Poincare (no match)`
- `grep -rn "IsC1Submanifold|IsSimonSubmanifold" simongmt/Poincare --include=*.lean | grep theorem`
- `diff local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean GMT/Ch03/Contract.lean (identical)`
- `python3 over runs/.../dag.json: lean_name and lean_statement of every DAG node (collision check)`
- `lake env lean /tmp/tc-decomp/Check.lean, Glue.lean, Children.lean (statement elaboration, parent glue from stubbed children and siblings, trial child proofs)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/GMT/Ch03/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-tangent-characterizations-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Data/Set/Lattice/Image.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/WeightedBlowUp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/TangentDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaCompletion.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaSubmanifoldExample.lean`

Snapshot: project d09bc8a (its Contract.lean is byte-identical to the workspace contract), Mathlib 25730c7c, plus the pinned simongmt package.

Reusable declarations found, by child:
- (1) SimonGMT Chapter04: hausdorff_blowUp_image (H^n(eta_{x,r}(S)) = ofReal(r^-1)^n H^n(S) for arbitrary S), blowUpHomeomorph, map_inverse_blowUp_carrier (push-forward of H^n restricted to eta(M) by eta^-1 equals ofReal(r^-1)^n times H^n restricted to M). Mathlib: euclideanHausdorffMeasure_homothety_image, Isometry.euclideanHausdorffMeasure_image, MeasurableEmbedding.integral_map, integral_smul_measure.
- (2) Mathlib: withDensity_apply, withDensity_apply_eq_zero', integral_withDensity_eq_integral_toReal_smul0, Measure.restrict_apply0', ae_restrict_mem0, Integrable.lintegral_lt_top. SimonGMT's RectifiableVarifold.integral_weighted_blowUp is the varifold-specific model of child (2c).
- (3) SimonGMT: Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn (arbitrary sets), Chapter02.area_image_null_of_lipschitzOn (single Lipschitz-on-set map only). Mathlib: EuclideanSpace.euclideanHausdorffMeasure_eq_volume, TopologicalSpace.isOpen_biUnion_countable.
- (4) Mathlib: ContDiffAt.exists_lipschitzOnWith (C1 implies locally Lipschitz on open sets), measure_biUnion_null_iff. SimonGMT's IsSimonSubmanifold.nonempty_volumeAtlas is an alternative countable-atlas route.
- Parent glue: SimonGMT countablyRectifiable_of_measure_zero, CountablyRectifiable.mono; Mathlib ae_restrict_iff'0, withDensity_absolutelyContinuous, integrableOn_const.

No match: neither library states the blow-up change of variables for an arbitrary set and integrand, the null-image lemma for maps that are only locally Lipschitz on an open set, or the chartwise a.e. transfer over an IsC1Submanifold cover. These are therefore supplied as children (1), (3) and (4).

Compilation checks: all four child statements elaborate. Trial proofs of all four children compiled (exit 0); child (1) imported Poincare.SimonGMT.Chapter04.WeightedBlowUp, whose oleans are present in .lake/packages/simongmt. The parent compiled from the children together with the stubbed sibling interfaces.

Collision check: no proposed lean_name collides with any lean_name in dag.json.
