# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.cube_poincare-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 2, Lemma 2.7 (Poincaré inequality for BV functions on bounded convex sets) and its printed proof (chapter-02.txt, "2.7 Lemma" and "Proof:"), applied on the unit cube with θ = 1/2, together with the choice (31) and the bound (35) of the integer β_F in Simon's proof of the Deformation Theorem 5.1 (parent step 7, (31)–(32), (35)). The printed proof of 2.7 shrinks U to a convex W depending on u; here W is a concentric cube, whose smooth Poincaré constant is bounded by that of the unit cube, so the final constant depends only on n.

Notation. n := m + 1, Q₁ := {y ∈ ℝⁿ : 0 < y_i < 1 for all i} (Euclid (m + 1), Lebesgue measure Lⁿ = volume, Lⁿ(Q₁) = 1), div g := trace of Dg. For δ ∈ [0, 1/4] let Q_δ := (δ, 1 − δ)ⁿ. Let u be integer-valued and integrable on Q₁, and V ∈ ℝ with ∫_{Q₁} u div g ≤ V for every C^∞ map g : ℝⁿ → ℝⁿ with compact support in Q₁ and |g| ≤ 1 (hypothesis (H)). Applying (H) to g = 0 gives V ≥ 0; applying it to −g gives |∫_{Q₁} u div g| ≤ V for all such g.

1. Integer median (Simon (31)). F(b) := Lⁿ(Q₁ ∩ {u ≤ b}) is nondecreasing in b ∈ ℤ, tends to 0 as b → −∞ and to 1 as b → +∞ (u is finite everywhere and Lⁿ(Q₁) = 1; continuity of measure). Let β be the least integer with F(β) ≥ 1/2. Then Lⁿ(Q₁ ∩ {u ≤ β}) ≥ 1/2, and since u is integer-valued, {u ≥ β} = Q₁ ∖ {u ≤ β − 1} has measure 1 − F(β − 1) > 1/2. So min{Lⁿ(Q₁ ∩ {u ≥ β}), Lⁿ(Q₁ ∩ {u ≤ β})} ≥ 1/2.

2. The bound |β| ≤ 2∫_{Q₁}|u| (Simon (35)). If β > 0 then |u| ≥ β on {u ≥ β}, so ∫|u| ≥ β·Lⁿ{u ≥ β} ≥ β/2. If β < 0 then |u| ≥ |β| on {u ≤ β}, so ∫|u| ≥ |β|/2. If β = 0 there is nothing to prove.

3. Smooth Poincaré inequality on cubes. For a cube Q of side s and v ∈ C¹ on a neighbourhood of Q̄, with v̄ := Lⁿ(Q)⁻¹∫_Q v: ∫_Q |v − v̄| ≤ n·s·∫_Q |Dv|. Proof: ∫_Q|v − v̄| ≤ Lⁿ(Q)⁻¹∫_Q∫_Q|v(x) − v(y)| dx dy. Write v(x) − v(y) = Σ_{i=1}^n [v(w^{i−1}) − v(w^i)] with w^i := (y_1, …, y_i, x_{i+1}, …, x_n), and |v(w^{i−1}) − v(w^i)| ≤ ∫ over the segment between x_i and y_i of |∂_i v|. Integrating over x, y ∈ Q (Fubini) bounds the i-th term by s·Lⁿ(Q)·∫_Q|∂_i v|. Summing over i gives the claim. Consequently, for every β' with min{Lⁿ(Q ∩ {v ≥ β'}), Lⁿ(Q ∩ {v ≤ β'})} ≥ θLⁿ(Q) (0 < θ ≤ 1): if β' ≥ v̄ then v − v̄ ≥ β' − v̄ ≥ 0 on {v ≥ β'}, so (β' − v̄)θLⁿ(Q) ≤ ∫_Q|v − v̄|; symmetrically if β' < v̄; hence ∫_Q|v − β'| ≤ ∫_Q|v − v̄| + |v̄ − β'|Lⁿ(Q) ≤ (1 + θ⁻¹)∫_Q|v − v̄|. The same two statements hold, with the same proofs, for v ∈ L¹(Q) in place of a C¹ function when the right side ∫|Dv| is replaced by the limit used in step 5.

4. Shrinking (as in the printed proof). Choose δ ∈ (0, 1/4] so small that Lⁿ(Q₁ ∖ Q_δ) ≤ 1/4 and ∫_{Q₁∖Q_δ}|u − β| ≤ ½∫_{Q₁}|u − β| (absolute continuity of the integral). Then, with W := Q_δ (a cube of side s := 1 − 2δ ≤ 1 and Lⁿ(W) ≤ 1): Lⁿ(W ∩ {u ≥ β}) ≥ 1/2 − 1/4 ≥ ¼Lⁿ(W), likewise for {u ≤ β}, and ∫_{Q₁}|u − β| ≤ 2∫_W|u − β|.

5. Mollification (Simon Ch. 2, 2.5). Let φ be a symmetric mollifier and u_ε := φ_ε ∗ (u·1_{Q₁}) for 0 < ε < δ. On a neighbourhood of W̄, u_ε is C^∞, and u_ε → u in L¹(W) as ε ↓ 0. For every C^∞ g with compact support in W and |g| ≤ 1, ∫_W Du_ε·g = −∫ u_ε div g = −∫ u div(φ_ε ∗ g) ≤ V, because φ_ε ∗ g is C^∞ with compact support in Q₁ (ε < δ) and |φ_ε ∗ g| ≤ 1, and (H) applies to −(φ_ε ∗ g). Taking the supremum over such g (|Du_ε| is continuous, so ∫_W|Du_ε| is the supremum of ∫_W Du_ε·g over C^∞ compactly supported g with |g| ≤ 1, by approximating Du_ε/|Du_ε| truncated) gives ∫_W|Du_ε| ≤ V.
 By step 3 on W: ∫_W|u_ε − ū_ε| ≤ n·s·V ≤ nV, where ū_ε := Lⁿ(W)⁻¹∫_W u_ε → ū := Lⁿ(W)⁻¹∫_W u. Letting ε ↓ 0 (L¹ convergence): ∫_W|u − ū| ≤ nV.

6. Median replacement and conclusion (Simon 2.7 with θ = 1/4 on W, then (32)). By step 4, β satisfies min{Lⁿ(W ∩ {u ≥ β}), Lⁿ(W ∩ {u ≤ β})} ≥ ¼Lⁿ(W), so the argument of step 3 (applied to u ∈ L¹(W) and its mean ū) gives ∫_W|u − β| ≤ (1 + 4)∫_W|u − ū| ≤ 5nV. Hence ∫_{Q₁}|u − β| ≤ 2∫_W|u − β| ≤ 10nV.

So the statement holds with c := 10n = 10(m + 1) > 0, which depends only on m, and the integer β of step 1, which also satisfies |β| ≤ 2∫_{Q₁}|u| by step 2. ∎

## Key steps

1. The least integer β with Lⁿ{u ≤ β} ≥ 1/2 is an integer median: both {u ≥ β} and {u ≤ β} have measure ≥ 1/2, which gives |β| ≤ 2∫|u|.
2. Smooth L¹ Poincaré inequality on cubes, ∫|v − v̄| ≤ n·s·∫|Dv|, by coordinate paths, and replacement of the mean by any θ-median with factor 1 + θ⁻¹.
3. Shrink to a concentric cube W = Q_δ keeping half of ∫|u − β| and the median property with θ = 1/4; mollify (supports stay in Q₁) to get ∫_W|Du_ε| ≤ V; pass to the limit.
4. Conclude ∫_{Q₁}|u − β| ≤ 2·5·n·V, i.e. c = 10n.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (mode local-project, project b4d606db, mathlib 25730c7c)`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `rg -l -i "latticeFace|DeformationTheorem|deformation theorem|skeleton|retraction" local-references/123e8435b4a2469b/project -g "*.lean" (only GMT/Ch06/Contract.lean and GMT/Ch06/Submission.lean)`
- `rg -n "latticeFace|def DeformationTheorem|IsLatticeChain|pushforward|homotopy|Poincar" local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `rg -n "theorem hausdorffMeasure_smul₀|theorem integral_map_equiv|theorem restrict_map|exists_disjoint_subfamily_covering_enlargement|theorem extend_real|theorem cthickening_cthickening_subset|theorem cthickening_eq_biUnion_closedBall|theorem lipschitz_infDist_pt|theorem ae_differentiableAt" local-references/123e8435b4a2469b/mathlib/Mathlib`
- `rg -c for extend_pi, integral_lineDeriv_mul_eq, exists_partition_approximatesLinearOn_of_hasFDerivWithinAt, image_of_continuousOn_injOn, ae_convolution_tendsto_right_of_locallyIntegrable, euclideanHausdorffMeasure_image, hausdorffMeasure_image_le, measure_compl_support, measurable_fderiv in Mathlib (all present)`
- `grep -n "theorem integral_lineDeriv_mul_eq" Mathlib/Analysis/Calculus/Rademacher.lean; sed -n 1,140p Mathlib/Geometry/Euclidean/Volume/Measure.lean (μHE[d], isometry invariance)`
- `grep -n "^def |^theorem" SimonGMT Chapter06/{Product,GeometricPointProduct,AffineCurrentPushforward,Currents,Mass,CurrentLocalEquality,Forms}.lean (only affine push-forward and point products; no Lipschitz push-forward, no [[(0,1)]] × T, no homotopy formula)`
- `grep -rn "theorem [a-zA-Z_.]*area" .lake/packages/simongmt/Poincare/SimonGMT (Chapter02 area formulas: injective_area_formula_lipschitz, area_image_criticalSet_eq_zero, ...)`
- `grep -n "def HasApproximateTangentSpaceAt|def CountablyRectifiable|def blowUpMap" SimonGMT/Chapter03/Rectifiable.lean`
- `rg -c exteriorDerivativeOn_pullbackFormWithin, exteriorDerivative_affinePullbackForm, WeaklyConvergesOn.boundary, countablyRectifiable_of_measure_zero in SimonGMT (present)`
- `python3 -I scans of dag.json (1366 nodes, 2026-10-13T14:15Z): statuses and frozen types of dor_imrep_massOn_eq_measure_and_support, cmc_imRep_locality_restrict_sub (accepted), dor_lmb_fc_im_series (decomposing), dor_lmb_slicing_lipschitz (speculative-ready), accepted dpf_*/ptd_*/pit_*/dtc_* helpers; byte-identical types of cmcdt_skeleton_retraction, cmcdt_good_center, dimred_mbl_dt_*; freshness of the dor_lmb_fcd_* names`
- `python3 -I parse of nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1/decomposition-v2.json and nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-convergence-a1/decomposition-v2.json`
- `sed -n 340,960p and 1400,1965p book/chapter-06.txt; sed -n 470,700p book/chapter-02.txt`
- `sed -n 6660,6760p and 3210,3260p /runtime/flows/gmt-claude-9a0895c8c5e1/_recursive_lean/runtime.py (_existing_lean_name_problem, accepted-child overlay scoping)`
- `lake env lean /tmp/dfm-decomp/lean/Challenge_*.lean (12 exact comparator challenges), AllProps.lean, Assembly.lean and UnitAssembly.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Product.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/GeometricPointProduct.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-cab3e79dc1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-convergence-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-9a0895c8c5e1/_recursive_lean/runtime.py`
- `/tmp/dfm-decomp/lean/Assembly.lean`
- `/tmp/dfm-decomp/lean/UnitAssembly.lean`
- `/tmp/dfm-decomp/lean/AllProps.lean`

Snapshot: project b4d606db, mathlib 25730c7c; the snapshot Ch07 Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. Neither the snapshot nor SimonGMT contains a proved Deformation Theorem, Lemma 5.4, a Lipschitz push-forward of currents, the product [[(0,1)]] × T, or the homotopy formula: SimonGMT Chapter06 provides only affine push-forwards and point products (plus currents, boundary, massOn, support, weak convergence with lower semicontinuity); Chapter02 provides area formulas for Lipschitz maps; Chapter03 the literal approximate-tangent-space definition. The snapshot's GMT/Ch06/Contract.lean has only sorry-frozen latticeFace/IsLatticeChain/DeformationTheorem definitions (the same unit and ρ-cells as the child face formulas), not imported by GMT.Ch07.Submission. Every Mathlib lemma cited in the child proofs exists in the pinned snapshot (Vitali covering, cthickening lemmas, lipschitz_infDist_pt, integral_map_equiv, MeasurableEquiv.restrict_map, hausdorffMeasure_smul₀, integral_lineDeriv_mul_eq, Rademacher, measurable_fderiv, convolution a.e. convergence, Isometry.euclideanHausdorffMeasure_image, measure_compl_support). Reuse: dor_imrep_massOn_eq_measure_and_support and cmc_imRep_locality_restrict_sub are accepted with byte-identical frozen types (standard axioms per acceptance); dor_lmb_fc_im_series (decomposing) and dor_lmb_slicing_lipschitz (speculative-ready) are passed as exact-type antecedents. Lean: all 12 child types compile as exact comparator challenges; parent_assembly and unit_assembly compile with axioms [propext, Classical.choice, Quot.sound].
