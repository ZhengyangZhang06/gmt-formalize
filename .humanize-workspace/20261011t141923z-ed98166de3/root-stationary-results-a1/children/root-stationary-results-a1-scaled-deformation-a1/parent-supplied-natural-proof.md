# Parent-supplied natural-language proof

- Parent DAG node: `root.stationary_results-a1`
- Child DAG node: `root.stationary_results-a1.scaled_deformation-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof II.2 step 6 (the test deformations φ_t(x) = x + λtζ(x)e). Simon's remark after 5.4 (p. 63), "by the first variation formula 5.3 this is equivalent to ∫_M div_M X dHⁿ = 0 whenever X is C¹ on U with support X a compact subset of U", presupposes that such deformations are admissible; this is proved here.

Setting. U ⊆ ℝᴺ open, Y : ℝᴺ → ℝᴺ of class C² with compact support, K := tsupport Y ⊆ U.

1. K is compact (HasCompactSupport Y means that tsupport Y is compact) and K ⊆ U. If x ∉ K then Y vanishes on the open neighbourhood Kᶜ of x, so Y(x) = 0 and DY(x) = 0.
2. DY is continuous (Y ∈ C²) and vanishes outside the compact set K (HasCompactSupport.fderiv), hence bounded: L := sup over x of ‖DY(x)‖ < ∞. Put c := 1/(L + 1) > 0, so that c·L < 1.
3. By the mean value inequality on the convex space ℝᴺ (lipschitzWith_of_nnnorm_fderiv_le), ‖Y(x) − Y(x′)‖ ≤ L‖x − x′‖ for all x, x′.
4. Define φ t x := x + (c t)•Y(x). Fix t ∈ (−1, 1) and put s := c t and κ := |s| L ≤ c L < 1, so φ t = id + s Y.
 (i) φ t is injective: if x + sY(x) = x′ + sY(x′), then ‖x − x′‖ = |s|·‖Y(x′) − Y(x)‖ ≤ κ‖x − x′‖, so x = x′.
 (ii) φ t is surjective onto ℝᴺ: for z ∈ ℝᴺ the map T_z(x) := z − sY(x) is κ-Lipschitz with κ < 1 on the complete space ℝᴺ, so it has a fixed point x (Banach fixed point theorem, ContractingWith.fixedPoint); then x + sY(x) = z.
 (iii) φ t x = x for every x ∉ K, since Y(x) = 0.
 (iv) BijOn (φ t) U U. MapsTo: let x ∈ U. If x ∉ K, then φ t x = x ∈ U. If x ∈ K and φ t x ∉ K, then by (iii) φ t (φ t x) = φ t x, so injectivity (i) gives φ t x = x ∈ K, a contradiction; hence φ t x ∈ K ⊆ U. InjOn: by (i). SurjOn: let z ∈ U and choose x with φ t x = z by (ii). If x ∉ K then z = φ t x = x, so x ∈ U; if x ∈ K then x ∈ U. In both cases z ∈ φ t '' U.
 (v) For every x, fderiv ℝ (φ t) x = id + s·DY(x) (derivative of a sum and of a constant multiple). If (id + s DY(x))v = 0 then ‖v‖ = |s|·‖DY(x)v‖ ≤ κ‖v‖, so v = 0. Thus fderiv ℝ (φ t) x is an injective linear endomorphism of the finite-dimensional space ℝᴺ, hence bijective (LinearMap.injective_iff_surjective).
5. Regularity: (t, x) ↦ x + (c t)•Y(x) is C² on ℝ × ℝᴺ (built from the C² maps p ↦ p.2, p ↦ c·p.1 and p ↦ Y(p.2) by addition and scalar multiplication), in particular ContDiffOn ℝ 2 on (−1,1) ×ˢ U.
6. φ 0 x = x + 0•Y(x) = x for every x, in particular for x ∈ U.
7. Steps 1, 4(iii), 4(iv), 4(v), 5 and 6 are exactly the clauses of IsAdmissibleDeformation 2 U K φ: U open, K compact, K ⊆ U, C² on (−1,1) × U, φ 0 = id on U, φ t x = x for t ∈ (−1,1) and x ∉ K, and for each t ∈ (−1,1), BijOn (φ t) U U and fderiv ℝ (φ t) x bijective for x ∈ U.
8. Initial velocity: for fixed x, t ↦ x + (c t)•Y(x) is affine in t with derivative c•Y(x), so initialVelocity φ x = deriv (t ↦ φ t x) 0 = c•Y(x). Together with c > 0 this proves the claim.

## Key steps

1. L := sup‖DY‖ < ∞ (compact support), c := 1/(L+1); Y is L-Lipschitz by the mean value inequality.
2. For |t| < 1, φ_t = id + ctY is injective (contraction estimate), surjective (Banach fixed point) and the identity off K.
3. A bijection of ℝᴺ fixing Kᶜ pointwise maps K into K, hence BijOn (φ t) U U; Dφ_t = I + ctDY is injective, hence bijective.
4. φ is C², φ_0 = id, and the initial velocity is c·Y.

## Reference use

### local-project

Queries:
- `cat -n GMT/Ch02/Contract.lean; diff GMT/Ch02/Contract.lean GMT/Ch02/Submission.lean; cat GMT/Ch02/README.md`
- `grep -rn "μHE\[" mathlib/Mathlib --include=*.lean | grep -E "notation|def "; sed -n 1,140p mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `cat -n simongmt/Poincare/SimonGMT/Chapter02/{Submanifold,SubmanifoldCalculus,SecondFundamentalForm,SecondFundamentalFormCalculus,SubmanifoldIntegral,SubmanifoldTopology,WeightedArea,Area}.lean; grep -n 'injective_area_formula_of_injective_derivative' AreaFormula.lean`
- `grep -rn "theorem ContDiffAt.isSymmSndFDerivAt\|theorem HasFDerivWithinAt.unique_on\|theorem ContDiffAt.to_localInverse\|theorem LipschitzOnWith.hausdorffMeasure_image_le\|theorem HasCompactSupport.fderiv\|theorem finrank_euclideanSpace_fin" mathlib/Mathlib`
- `grep -rn tangentConeAt mathlib/Mathlib --include=*.lean | grep -E "theorem|lemma" | grep -iE "deriv|curve|segment|mem_tangentCone"; grep -rn mapsTo_tangent mathlib/Mathlib`
- `grep -rn "integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable\|integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable" mathlib/Mathlib; grep -n "theorem\|lemma" mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `grep -rn "Submission\.\|stationary_imp_mean_curvature_zero\|second_fundamental_form_chart_formula\|submanifold_divergence_identity_compact\|deformation_velocity_acceleration_regularity" project simongmt/Poincare; python3 -I lean_name collision check against dag.json`
- `python3 -I gen_checks.py (replays verifier gmt-compare.py contract_scope/child_modules and lean_contract.validate_lean_statement for the 10 lean_statements); lake build GMT.Ch02.Submission; lake env lean NodeChallenge_00..09.lean; lake env lean AssemblyCheck.lean`
- `lake env lean LibCheck.lean: #print axioms Poincare.SimonGMT.Chapter02.{integral_area_formula_of_injective_derivative, IsSimonLocalRepresentation.area_formula, IsSimonLocalRepresentation.weighted_area_formula, IsSimonLocalRepresentation.exists_open_image_eq_inter, IsSimonLocalRepresentation.isEmbedding_chartMap, submanifoldDivergenceAt_eq_sum_inner, measurable_areaJacobianAt}; #check of every cited Mathlib lemma`
- `sed -n 1030,1420p book/chapter-02.txt (printed 4.18-5.12); read dag.json and nodes/root-stationary-results-a1/parent-child-handoff.json`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/Equiv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/TangentCone/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/NormDet.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SecondFundamentalForm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SecondFundamentalFormCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldTopology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/WeightedArea.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Area.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaFormula.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/stat-decomp2/AssemblyCheck.lean`

The frozen contract (Contract.lean lines 83-176 and 297-342) defines the key notions:
- B is fderivWithin of tangentProjection;
- H is the frame trace;
- IsStationaryIn is defined variationally.

Collision checks: the snapshot project has no Submission.* declarations and no declaration with any of the ten proposed names, and dag.json (50 nodes) has no lean_name collision.

SimonGMT supplies kernel-checked tools used by the children:
- WeightedArea.lean: integral_area_formula_of_injective_derivative and IsSimonLocalRepresentation.area_formula;
- SubmanifoldTopology.lean: IsSimonLocalRepresentation.exists_open_image_eq_inter and isEmbedding_chartMap;
- SubmanifoldCalculus.lean: submanifoldDivergenceAt_eq_sum_inner;
- measurable_areaJacobianAt.
#print axioms shows only propext, Classical.choice and Quot.sound for all of them.

SimonGMT has no divergence theorem on submanifolds (integral_submanifoldDivergence_eq_curvature_sub_boundary takes it as a hypothesis), no chart formula for the frame-free B, and nothing on admissible deformations. These are therefore genuine new obligations.

Mathlib 25730c7c supplies ContDiffAt.isSymmSndFDerivAt, HasFDerivWithinAt.unique_on, HasFDerivWithinAt.mapsTo_tangent_cone, tangentConeAt_mono, tangentConeAt_of_mem_nhds, ContDiffAt.toOpenPartialHomeomorph, ContDiffAt.to_localInverse, OpenPartialHomeomorph.contDiffAt_symm, integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable, LinearMap.normDet_ne_zero_tfae, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, LipschitzOnWith.hausdorffMeasure_image_le, ContractingWith.fixedPoint, HasCompactSupport.fderiv and ContDiffBump. exists_smooth_tsupport_subset does not exist, so it is not cited. setIntegral_eq_of_subset_of_forall_diff_eq_zero is deprecated, so the _sdiff_ name is cited.

Compile checks:
- All ten lean_statements pass the workflow validator and elaborate in the comparator-replayed contract scope; NodeChallenge_00..09 compiled with only sorry warnings.
- AssemblyCheck.lean proves the frozen parent type StationaryIffMeanCurvatureZero ∧ SecondVariationStationary from the children and the sibling types. Its axioms are sorryAx from the stubs plus propext, Classical.choice and Quot.sound.
- Glue examples that instantiate the children as their proofs use them also compile.
