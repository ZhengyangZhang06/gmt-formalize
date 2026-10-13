# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.good_center-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 6, proof of the Deformation Theorem 5.1, displays (1)–(7) (chapter-06.txt, "Proof of the Deformation Theorem" up to (7)); step 2 of the parent proof. The printed argument uses only that M(T⌞·) and M(∂T⌞·) are finite Borel measures, so it is stated here for two arbitrary finite Borel measures μ, μ' on ℝ^P (in the parent, μ = μ_T and μ' = μ_∂T, the measures of IMReps of T and ∂T).

Notation. n := m + 1 < P, ℓ := P − n ≥ 1. For an index set J ⊆ {0, …, P − 1} with |J| = n + 1 (there are N := binom(P, n + 1) such J) let S_J := span{e_i : i ∈ J} (an (n + 1)-dimensional coordinate subspace, Simon's S_j), p_J the orthogonal projection onto S_J (p_J(x)_i = x_i for i ∈ J, 0 otherwise), Z_J := ℤ^P ∩ S_J (integer vectors vanishing off J), q := (1/2, …, 1/2), x_J := p_J(q). ω_d := L^d(B_1(0)) and B_σ(g) denotes an open ball (in S_J when g ∈ S_J). For a ∈ ℝ^P, L*(a) := {w : w_i − a_i ∈ ℤ for at least n + 1 indices} is the set written in the statement and d_a := infDist(·, L*(a)).

1. Tube description. For every a and r > 0: {x : d_a(x) < r} = ⋃_J ⋃_{z∈Z_J} p_J⁻¹(B_r(p_J(a) + z)). Indeed L*(a) = ⋃_J ⋃_{z∈Z_J} A_{J,z} with A_{J,z} := {w : w_i = a_i + z_i for i ∈ J} = p_J⁻¹(p_J(a) + z) (a point with at least n + 1 coordinates in a_i + ℤ has such coordinates on some (n + 1)-set J), and dist(x, A_{J,z}) = |p_J(x) − p_J(a) − z| (the nearest point of A_{J,z} changes only the J-coordinates). d_a(x) < r iff some w ∈ L*(a) has |x − w| < r iff some A_{J,z} has dist(x, A_{J,z}) < r. In particular this set is open (so measurable).

2. Bad sets have small measure (Simon (1)–(4)). Fix β > 0 (chosen in step 4) and a finite Borel measure ν on ℝ^P. For each J let B_J(ν) be the set of g ∈ S_J with |g − x_J| < 1/4 for which some σ ∈ (0, 1/4) has ν(⋃_{z∈Z_J} p_J⁻¹(B_σ(g + z))) > βσ^{n+1}ν(ℝ^P). Claim: the outer (n + 1)-dimensional Lebesgue measure of B_J(ν) in S_J is at most 5^{n+1}ω_{n+1}β⁻¹; more precisely B_J(ν) ⊆ ⋃_k B_{5σ_k}(b_k) for countably many balls in S_J with Σ_k σ_k^{n+1} ≤ β⁻¹.
 If ν(ℝ^P) = 0, B_J(ν) = ∅. Otherwise choose for each b ∈ B_J(ν) a radius σ_b ∈ (0, 1/4) as in the definition. By the 5-times covering lemma (Simon Ch. 1, 3.4; Mathlib Vitali.exists_disjoint_subfamily_covering_enlargement applied to the balls B_{σ_b}(b) in S_J, radii bounded by 1/4) there is a pairwise disjoint subfamily {B_{σ_k}(b_k)}, countable because S_J is separable and the balls are open and disjoint, with B_J(ν) ⊆ ⋃_k B_{5σ_k}(b_k). The sets p_J⁻¹(B_{σ_k}(b_k + z)) (k, z ∈ Z_J) are pairwise disjoint: for the same z they are preimages of disjoint balls; for z ≠ z', |(b_k + z) − (b_{k'} + z')| ≥ |z − z'| − |b_k − b_{k'}| > 1 − 1/2 > σ_k + σ_{k'}, since b_k, b_{k'} ∈ B_{1/4}(x_J) and σ < 1/4. Summing the defining inequalities over k gives βν(ℝ^P)Σ_kσ_k^{n+1} ≤ Σ_k ν(⋃_z p_J⁻¹(B_{σ_k}(b_k + z))) ≤ ν(ℝ^P), so Σ_kσ_k^{n+1} ≤ β⁻¹ and L^{n+1}(⋃_k B_{5σ_k}(b_k)) ≤ Σ_k ω_{n+1}(5σ_k)^{n+1} ≤ 5^{n+1}ω_{n+1}β⁻¹.

3. Fubini (Simon (5)). With S_J^⊥ := span{e_i : i ∉ J} ((ℓ − 1)-dimensional; ℝ^P = S_J × S_J^⊥ isometrically, Lebesgue measure being the product), {a ∈ B_{1/4}(q) : p_J(a) ∈ B_J(ν)} ⊆ {a : p_J(a) ∈ ⋃_k B_{5σ_k}(b_k), |p_J^⊥(a − q)| < 1/4}, an open set of L^P-measure ≤ 5^{n+1}ω_{n+1}β⁻¹·ω_{ℓ−1}4^{1−ℓ} (for ℓ = 1, S_J^⊥ = {0} and the factor is 1).

4. Choice of a (Simon (5)–(7)). Choose β = β(P, m) > 0 so large that 2N·5^{n+1}ω_{n+1}ω_{ℓ−1}4^{1−ℓ}β⁻¹ < ω_P4^{−P} = L^P(B_{1/4}(q)). By steps 2–3 applied to ν = μ and ν = μ', the union over J of {a ∈ B_{1/4}(q) : p_J(a) ∈ B_J(μ) ∪ B_J(μ')} has outer measure < L^P(B_{1/4}(q)), so some a ∈ B_{1/4}(q) avoids it. For every J, p_J(a) ∈ S_J and |p_J(a) − x_J| = |p_J(a − q)| ≤ |a − q| < 1/4, so p_J(a) ∉ B_J(μ) means: for all σ ∈ (0, 1/4), μ(⋃_{z∈Z_J} p_J⁻¹(B_σ(p_J(a) + z))) ≤ βσ^{n+1}μ(ℝ^P); likewise for μ'. Also |a_i − 1/2| ≤ |a − q| < 1/4 for every i.

5. Conclusion (Simon (6), (7)). Let C := Nβ (a nonnegative real, regarded in ℝ≥0). For r ∈ (0, 1/4), step 1 and subadditivity give μ({d_a < r}) ≤ Σ_J μ(⋃_z p_J⁻¹(B_r(p_J(a) + z))) ≤ Nβr^{n+1}μ(ℝ^P), and the same for μ'. For r = 1/4: {d_a < 1/4} is the increasing union of the sets {d_a < 1/4 − 1/j} (j ≥ 5), so by continuity from below μ({d_a < 1/4}) = lim_j μ({d_a < 1/4 − 1/j}) ≤ lim_j Nβ(1/4 − 1/j)^{n+1}μ(ℝ^P) = Nβ(1/4)^{n+1}μ(ℝ^P), and likewise for μ'. Since n + 1 = m + 2 and C·ENNReal.ofReal(r^{m+2})·μ(univ) = Nβr^{n+1}μ(ℝ^P), both inequalities of the statement hold for every r ∈ (0, 1/4]. C depends only on P and m. ∎

## Key steps

1. The r-tube around L*(a) is the union over (n+1)-dimensional coordinate subspaces S_J and z ∈ ℤ^P ∩ S_J of the cylinders p_J⁻¹(B_r(p_J(a) + z)).
2. For each J the bad set of g ∈ S_J ∩ B_{1/4}(x_J) violating the β-bound at some radius is covered (5-times covering lemma) by balls B_{5σ_k}(b_k) with Σσ_k^{n+1} ≤ β⁻¹, using disjointness of the translated cylinders.
3. Fubini bounds the set of a ∈ B_{1/4}(q) with p_J(a) bad; for β = β(P, m) large the 2N exceptional sets do not exhaust B_{1/4}(q).
4. A good a satisfies μ({d < r}) ≤ Nβr^{n+1}μ(ℝ^P) for r < 1/4 (and r = 1/4 by continuity from below), likewise for μ'; C := Nβ.

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
