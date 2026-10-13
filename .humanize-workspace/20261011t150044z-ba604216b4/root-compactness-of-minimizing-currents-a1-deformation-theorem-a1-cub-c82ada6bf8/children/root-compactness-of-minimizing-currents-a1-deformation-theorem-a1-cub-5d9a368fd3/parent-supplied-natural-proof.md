# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1.bv_poincare-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1.bv_poincare-a1.unit_cube_volume-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the notation paragraph of the parent proof ("vol(Q₁) = 1", obtained from the measure-preserving identification Euclid n ≃ (Fin n → ℝ)), written out in full.

Notation. m ∈ ℕ, n := m + 1, Euclid n = EuclideanSpace ℝ (Fin n) with volume = Lebesgue measure, y_i the i-th coordinate of y, Q₁ := {y ∈ Euclid n : 0 < y_i < 1 for all i}.

1. Let ofLp : Euclid n → (Fin n → ℝ) be the canonical map sending a Euclidean vector y to its coordinate function i ↦ y_i (so (ofLp y) i = y_i for all i). It is a measurable linear bijection, and by Mathlib's PiLp.volume_preserving_ofLp (a copy of EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp) it is measure preserving from the volume of Euclid n to the volume of Fin n → ℝ, which is the product of the one-dimensional Lebesgue measures.
2. Let B := {w : Fin n → ℝ : w i ∈ (0, 1) for all i} = ∏_{i ∈ Fin n} (0, 1) (Set.pi univ (fun _ => Ioo 0 1)). Since y_i = (ofLp y) i, a point y ∈ Euclid n lies in Q₁ if and only if ofLp y ∈ B. Hence Q₁ = ofLp⁻¹(B).
3. B is measurable, being a finite product of open intervals (MeasurableSet.univ_pi with measurableSet_Ioo). For a measure preserving map, the measure of the preimage of a measurable set equals the measure of the set (MeasurePreserving.measure_preimage). Therefore vol(Q₁) = vol(ofLp⁻¹(B)) = vol(B).
4. By the product formula for open boxes (Real.volume_pi_Ioo), vol(B) = ∏_{i ∈ Fin n} ofReal(1 − 0) = ∏_{i ∈ Fin n} 1 = 1.
5. Combining steps 3 and 4, vol(Q₁) = 1. ∎

## Key steps

1. The coordinate map ofLp : Euclid (m+1) → (Fin (m+1) → ℝ) is measure preserving (PiLp.volume_preserving_ofLp).
2. Q₁ = ofLp⁻¹(∏_i (0,1)), and the box is measurable, so vol(Q₁) = vol(∏_i (0,1)).
3. Real.volume_pi_Ioo gives vol(∏_i (0,1)) = ∏_i ofReal(1 − 0) = 1.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD (25730c7c759d108ef87ab70af2342a196760f79d, matches manifest)`
- `rg -l 'cmcdt_cbm_bvp' local-references/123e8435b4a2469b/ (no match); rg -n 'cmcdt_cbm_bvp|osc_le_of_l1_approx|mean_dev_le_osc|unit_cube_volume|osc_le_of_inner_cubes' project mathlib/Mathlib -g '*.lean' (no match); python3 scan of dag.json (1582 nodes) lean_name and theorems fields for the four proposed names (no collision)`
- `rg -n -i 'BVPoincare|poincar[eé] inequality|poincare_ineq' project -g '*.lean'`
- `rg -n -i 'integral.*\|.* - .*\|.*≤.*∫.*∫|abs_sub_average|integral_abs_sub_average|average_le_integral|norm_sub_average' mathlib/Mathlib -g '*.lean' (no match)`
- `rg -n 'theorem tendsto_setIntegral_of_monotone$|theorem setIntegral_prod |theorem PiLp.volume_preserving_ofLp|theorem volume_pi_Ioo |lemma Integrable.comp_fst|lemma Integrable.comp_snd|theorem Integrable.integral_prod_left|lemma integral_mono_of_nonneg|lemma abs_integral_le_integral_abs|theorem ContinuousOn.integrableOn_compact |theorem EuclideanSpace.norm_eq|theorem iUnion_prod_of_monotone|theorem prod_restrict' mathlib/Mathlib`
- `python3 scan of dag.json lean_statement fields for 'volume \{y : Euclid', '\|u x - u y\|', '\|v x - v y\|', 'δ < z i ∧ z i < 1 - δ' (hits only in sibling or unaccepted nodes)`
- `lake env lean /tmp/bvp-decomp/final/FinalCheck.lean (generated from the exact lean_statement strings: four children fully proved, parent frozen type derived from children + sorry'd siblings); lake env lean /tmp/bvp-decomp/final/FinalCheckAx.lean (siblings as axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Lattice/Image.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-c82ada6bf8/parent-child-handoff.json`
- `/tmp/bvp-decomp/final/FinalCheck.lean`
- `/tmp/bvp-decomp/final/FinalCheckAx.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) has the same Ch07 contract as the workspace Contract.lean and Submission.lean.

Nothing in it can be reused for this node:
- The only BV Poincaré statement is the Ch02 contract def BVPoincare (Simon 2.7). It is unproved (main_theorem := by sorry) and belongs to another chapter.
- Ch04 5.6 is a different, varifold Poincaré inequality.
- Mathlib has no mean-oscillation or Poincaré lemma of this form.
- No DAG node has an identical type. cmcdtfr_face_geometry contains vol(Q₁) = 1 only as one conjunct of a different, unaccepted type.

Mathlib supplies every tool the child proofs cite, all already inside the GMT.Ch07.Submission import closure, so no new imports are needed:
- PiLp.volume_preserving_ofLp, MeasurePreserving.measure_preimage, Real.volume_pi_Ioo;
- Integrable.comp_fst, Integrable.comp_snd, Integrable.integral_prod_left, Measure.prod_restrict, setIntegral_prod;
- tendsto_setIntegral_of_monotone, Set.iUnion_prod_of_monotone;
- integral_mono_of_nonneg, abs_integral_le_integral_abs;
- ContinuousOn.integrableOn_compact, EuclideanSpace.norm_eq.

The four proposed names are fresh.

After import GMT.Ch07.Submission, in the contract namespace and opens:
- All four child types elaborate, and all four children were fully proved with axioms propext, Classical.choice and Quot.sound only.
- The selected node's exact frozen type was derived from the children plus the two sibling contracts.
- With the siblings as axioms, the parent depends only on standard axioms plus Submission.cmcdt_cbm_smooth_approx and Submission.cmcdt_cbm_smooth_poincare.
