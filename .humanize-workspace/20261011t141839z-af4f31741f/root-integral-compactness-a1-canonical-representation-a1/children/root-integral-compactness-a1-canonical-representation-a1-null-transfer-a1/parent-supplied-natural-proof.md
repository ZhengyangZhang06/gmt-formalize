# Parent-supplied natural-language proof

- Parent DAG node: `root.integral_compactness-a1.canonical_representation-a1`
- Child DAG node: `root.integral_compactness-a1.canonical_representation-a1.null_transfer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 of the parent proof, stated for a general locally finite μ. Two small changes from that proof:
- its compact exhaustion K_p of U is replaced by an equivalent countable cover of U by balls with compact closure in U;
- its threshold θ(x) ≥ 1/k is phrased as upper density ≥ 1/(k+1). At points of M the upper density equals θ(x), by step 3.
The key ingredient is Simon Ch. 1, Theorem 3.3: for Borel regular μ on a metric space and A₁ ⊆ A₂, if Θ*^n(μ, A₂, x) ≥ t on A₁ then t·H^n(A₁) ≤ μ(A₂).
Lean prerequisite: Submission.lean must add three imports: Poincare.SimonGMT.Chapter01.DensityComparison, Poincare.SimonGMT.Chapter01.EuclideanHausdorffUpper and Poincare.SimonGMT.Chapter02.AreaLiteral. The comparator allows extra imports, and a lean4export comparison showed that these imports leave every Contract definition byte-identical.
Notation: ω := unitBallVolume n. realUnitBallVolume, dimensionalDensityQuotient, dimensionalUpperDensity and simonHausdorffOuterMeasureReal are SimonGMT's Poincare.SimonGMT.Chapter01 notions.

1. Normalizations.
(a) ω = realUnitBallVolume n. If n > 0, apply Chapter01.volume_euclidean_ball_eq at x = 0, r = 1: volume(ball 0 1) = realUnitBallVolume n · ofReal(1)^n. If n = 0, EuclideanSpace ℝ (Fin 0) is a one-point space, so ball 0 1 = univ and volume = dirac 0 (volume_euclideanSpace_eq_dirac); hence ω = 1 = realUnitBallVolume 0 (realUnitBallVolume_zero).
(b) For every A ⊆ ℝ^N, simonHausdorffOuterMeasureReal n A = μHE[n] A. This follows from (simonHausdorffMeasureReal n).toOuterMeasure = simonHausdorffOuterMeasureReal n (Chapter01.simonHausdorffMeasureReal_toOuterMeasure, valid since n ≥ 0) and simonHausdorffMeasureReal n = μHE[n] (Chapter02.simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure).
(c) Every Borel set is Carathéodory-measurable for the outer measure μ.toOuterMeasure (le_toOuterMeasure_caratheodory μ, with BorelSpace.measurable_eq).

2. Countable cover by balls of finite mass. For each y ∈ U pick r_y > 0 with closedBall y r_y ⊆ U (U is open: take half the radius of an open ball around y inside U). Let W_y := ball y r_y. Then μ(W_y) ≤ μ(closedBall y r_y) < ∞, because closed balls of ℝ^N are compact. ℝ^N is second countable, so there is a countable C ⊆ U with ⋃_{y∈C} W_y = ⋃_{y∈U} W_y (TopologicalSpace.isOpen_iUnion_countable). Since y ∈ W_y, this union contains U ⊇ Z.

3. Level sets. For y ∈ C and k ∈ ℕ let Z_{y,k} := {x ∈ Z ∩ W_y : (k+1)⁻¹ ≤ limsup_{ρ↓0} densityRatio n μ x ρ}. Every x ∈ Z lies in some W_y with y ∈ C (step 2). Its limsup is ≠ 0, so there is k with k⁻¹ < limsup (ENNReal.exists_inv_nat_lt), and (k+1)⁻¹ ≤ k⁻¹. Hence Z ⊆ ⋃_{y∈C} ⋃_{k∈ℕ} Z_{y,k}.

4. Small open neighbourhoods. Fix y ∈ C, k ∈ ℕ and ε ∈ (0, ∞].
- The measure ν := μ.restrict W_y has ν(ℝ^N) = μ(W_y) < ∞. So ν is a finite Borel measure on a metric space, hence outer regular (Mathlib instance for finite measures on pseudo-metrizable spaces).
- ν(Z_{y,k}) ≤ μ(Z_{y,k}) ≤ μ(Z) = 0 < ε.
- By outer regularity, which holds for arbitrary sets (Set.exists_isOpen_lt_of_lt), there is an open O' ⊇ Z_{y,k} with ν(O') < ε.
Put O := O' ∩ W_y. Then O is open, Z_{y,k} ⊆ O (because Z_{y,k} ⊆ W_y), and μ(O) = ν(O') < ε (Measure.restrict_apply, O' being measurable).

5. Densities relative to O. Let x ∈ Z_{y,k}. O is open and contains x, so ball x η ⊆ O for some η > 0. For 0 < ρ < η, closedBall x ρ ⊆ ball x η ⊆ O, so μ(O ∩ closedBall x ρ) = μ(closedBall x ρ). By 1(a) and ofReal(ρ)^(n:ℝ) = ofReal(ρ)^n (ENNReal.rpow_natCast), dimensionalDensityQuotient μ n O x ρ = μ(O ∩ closedBall x ρ)/(realUnitBallVolume n · ofReal(ρ)^n) equals densityRatio n μ x ρ for every ρ ∈ (0, η). That interval belongs to 𝓝[>] 0 (Ioo_mem_nhdsGT). Therefore (limsup_congr) dimensionalUpperDensity μ n O x = limsup_{ρ↓0} densityRatio n μ x ρ ≥ (k+1)⁻¹.

6. Comparison theorem. Use Simon's Theorem 3.3 in the form Chapter01.mul_simonHausdorff_le_of_le_dimensionalUpperDensity. It holds in any metric space, for any outer measure whose Carathéodory σ-algebra contains the Borel sets, with arbitrary sets A₁, A₂ and threshold t ∈ [0,∞]. Apply it to:
- the outer measure μ.toOuterMeasure (allowed by 1(c)) and real dimension n ≥ 0;
- A₁ := Z_{y,k}, A₂ := O and t := (k+1)⁻¹, with the density hypothesis from step 5.
This gives (k+1)⁻¹ · simonHausdorffOuterMeasureReal n (Z_{y,k}) ≤ μ(O). By 1(b) and step 4, (k+1)⁻¹ · μHE[n](Z_{y,k}) ≤ μ(O) < ε.

7. Since ε > 0 was arbitrary, (k+1)⁻¹ · μHE[n](Z_{y,k}) = 0 (le_of_forall_gt_imp_ge_of_dense). As k+1 ≠ ∞, (k+1)⁻¹ ≠ 0 (ENNReal.inv_ne_zero), so μHE[n](Z_{y,k}) = 0.

8. By step 3 and monotonicity, μHE[n](Z) ≤ μHE[n](⋃_{y∈C} ⋃_k Z_{y,k}). This is 0 by countable subadditivity over the countable index set C × ℕ (measure_biUnion_null_iff with C countable, then measure_iUnion_null_iff over k). ∎

Lean route: verified without sorry in a scratch copy, about 110 lines including the two normalization lemmas; axioms propext/Classical.choice/Quot.sound.

## Key steps

1. Normalizations: unitBallVolume n = realUnitBallVolume n; simonHausdorffOuterMeasureReal n = μHE[n] as outer measures; Borel sets are Carathéodory-measurable for μ.
2. Countably many balls W_y of finite μ-mass with compact closure in U cover Z; split Z into Z_{y,k} = Z ∩ W_y ∩ {upper density ≥ 1/(k+1)}.
3. Outer regularity of the finite measure μ⌞W_y gives an open O ⊇ Z_{y,k} with μ(O) < ε.
4. At points of Z_{y,k} ⊆ O (O open), Simon's upper density of μ relative to O equals limsup densityRatio n μ x ≥ 1/(k+1).
5. Simon 1.3.3 (mul_simonHausdorff_le_of_le_dimensionalUpperDensity) gives (k+1)⁻¹ H^n(Z_{y,k}) ≤ μ(O) < ε, so H^n(Z_{y,k}) = 0.
6. Countable subadditivity gives H^n(Z) = 0.

## Reference use

### local-project

Queries:
- `cat local-references/5a882a57db723346/manifest.json (mode local-project, project_commit 63436ae63eb6a2fd7525bef73c73cf88e2cd7e93, mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum snapshot project/GMT/Ch08/Contract.lean, workspace GMT/Ch08/Contract.lean, GMT/Ch08/Submission.lean (all 2e5cd5b3566b37c487f8a2f4ea90b5039601a3212077ada1cab6cd715556c487)`
- `rg -n 'HasTangentPlane|densityRatio|planeVarifoldMeasure' project/GMT/Ch08/Contract.lean`
- `rg -n 'μHE\[|Isometry.euclideanHausdorffMeasure_image|InnerProductSpace.euclideanHausdorffMeasure_eq_volume|euclideanHausdorffMeasure_zero' mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n 'theorem _root_.Set.exists_isOpen_lt_of_lt|of_pseudoMetrizableSpace_of_isFiniteMeasure' mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `rg -n 'theorem le_toOuterMeasure_caratheodory' mathlib/Mathlib/MeasureTheory/Measure/OuterMeasure.lean; rg -n 'theorem limsup_congr' mathlib/Mathlib/Order/LiminfLimsup.lean; rg -n 'measure_biUnion_null_iff|measure_iUnion_null_iff' mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `rg -n 'theorem addHaar_closedBall' mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean; rg -n 'theorem isOpen_iUnion_countable' mathlib/Mathlib/Topology/Bases.lean; rg -n 'volume_euclideanSpace_eq_dirac|theorem measurePreserving' mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `grep -n 'structure Varifold|isOpen_domain|def weight|weight_finite_on_compact|instCompactSpace|finrank_plane' simongmt Chapter08/Varifold.lean`
- `grep -n 'theorem mul_simonHausdorff_le_of_le_dimensionalUpperDensity|theorem simon_theorem_3_3|^variable' simongmt Chapter01/DensityComparison.lean; grep -n 'def dimensionalDensityQuotient|def dimensionalUpperDensity' Chapter01/Densities.lean; grep -n 'def realUnitBallVolume|simonHausdorffMeasureReal_toOuterMeasure|realUnitBallVolume_zero|def simonHausdorffOuterMeasureReal' Chapter01/Hausdorff.lean; grep -n 'realUnitBallVolume_nat_eq|volume_euclidean_ball_eq' Chapter01/EuclideanHausdorffUpper.lean; grep -n 'simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure' Chapter02/AreaLiteral.lean`
- `python3 dag.json scan for related frozen types and statuses (frt_weight_blowup_tendsto comparing; tgc_plane_closedBall_hausdorff, frt_tangent_plane_hasDensity, allard_tc_tangent_plane_density, frt_hausdorff_null_of_weight_null not accepted); grep -rho 'intcpt_[A-Za-z0-9_]*' run dir (no intcpt_canon_* except intcpt_canonical_tangent_representation)`
- `git show b951e87c:GMT/Ch08/Submission.lean (existing proof of the identical weight-blowup type)`
- `grep -n contract_scope/child_modules/candidate_inputs verifier/gmt-compare.py; read verifier/comparator/Comparator/Compare.lean (recursive constant equality) and Main.lean (safeExport via lean4export)`
- `lake env lean Test/Assembly.lean (comparator scope replay: 4 child stubs, NodeChallenge-form checks, parent assembly without own sorry)`
- `lake env lean Test/Imports.lean (Chapter01.DensityComparison, EuclideanHausdorffUpper, Chapter02.AreaLiteral lemmas absent from Submission's import closure)`
- `lake env lean Test/C2.lean, Test/B.lean, Test/C1.lean, Test/Full.lean (sorry-free chain; #print axioms: propext, Classical.choice, Quot.sound)`
- `python3 -I validate_lean_statement (verifier/lean_contract.py) on the 4 lean_statements`
- `lake env lean GMT/Ch08/{Contract,Submission+3 imports}.lean -o …; lake env lean4export GMT.Ch08.Contract / GMT.Ch08.Submission -- GMT.Ch08.main_theorem; diff (only the sorry tag of main_theorem differs)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/project/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/OuterMeasure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/local-references/5a882a57db723346/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/GMT/Ch08/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter08/Varifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/DensityComparison.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Densities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/EuclideanHausdorffUpper.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.lake/packages/simongmt/Poincare/SimonGMT/Chapter02/AreaLiteral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/comparator/Comparator/Compare.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/comparator/Main.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-canonical-representation-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-canonical-representation-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-allard-tangent-cones-a1-tangent-plane-density-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch08/.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-first-rectifiability-a1-weight-blowup-a1/comparison-identity-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-08.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/tmp/canon-decomp-UcXiqH/Test/Assembly.lean`
- `/tmp/canon-decomp-UcXiqH/Test/Imports.lean`
- `/tmp/canon-decomp-UcXiqH/Test/C2.lean`
- `/tmp/canon-decomp-UcXiqH/Test/B.lean`
- `/tmp/canon-decomp-UcXiqH/Test/C1.lean`
- `/tmp/canon-decomp-UcXiqH/Test/Full.lean`
- `/tmp/canon-imports-zUDhY3/GMT/Ch08/Submission.lean`
- `/tmp/canon-exports/contract.ndjson`
- `/tmp/canon-exports/submission_extra_imports.ndjson`

The snapshot pins project 63436ae6 and Mathlib 25730c7c. Its Contract is byte-identical to the workspace Contract and Submission.
All cited lemmas exist with suitable hypotheses:
- Mathlib: Isometry.euclideanHausdorffMeasure_image, InnerProductSpace.euclideanHausdorffMeasure_eq_volume, Measure.addHaar_closedBall, LinearIsometryEquiv.measurePreserving, volume_euclideanSpace_eq_dirac, Set.exists_isOpen_lt_of_lt (arbitrary sets), the outer-regularity instance for finite measures on pseudo-metrizable spaces, TopologicalSpace.isOpen_iUnion_countable, le_toOuterMeasure_caratheodory, limsup_congr, measure_biUnion_null_iff and measure_iUnion_null_iff.
- SimonGMT: Varifold.isOpen_domain, Varifold.weight_finite_on_compact, Grassmannian.finrank_plane, Chapter01.mul_simonHausdorff_le_of_le_dimensionalUpperDensity (Simon 1.3.3 for arbitrary sets), Chapter01.simonHausdorffMeasureReal_toOuterMeasure, realUnitBallVolume_zero, volume_euclidean_ball_eq and Chapter02.simonHausdorffMeasureReal_nat_eq_euclideanHausdorffMeasure.
- Three of these modules are outside Submission's import closure: DensityComparison, EuclideanHausdorffUpper and AreaLiteral. Adding them to Submission.lean is allowed by gmt-compare.py. A lean4export diff of main_theorem's dependency closure shows they leave every Contract definition byte-identical.
In the comparator's replayed Contract scope, the four child lean_statements elaborate in NodeChallenge form and pass validate_lean_statement. Each child was proved without sorry. The parent's frozen type then follows by a short assembly. #print axioms gives only propext, Classical.choice and Quot.sound.
Identical types exist in other DAG branches but none is accepted, so fresh intcpt_canon_* names are used. They do not occur anywhere in the run directory.
