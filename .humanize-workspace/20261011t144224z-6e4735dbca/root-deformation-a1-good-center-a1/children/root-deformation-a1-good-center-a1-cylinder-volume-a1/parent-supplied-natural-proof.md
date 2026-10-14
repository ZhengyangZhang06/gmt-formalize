# Parent-supplied natural-language proof

- Parent DAG node: `root.deformation-a1.good_center-a1`
- Child DAG node: `root.deformation-a1.good_center-a1.cylinder_volume-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Ch. 6, §5, printed "Proof of the Deformation Theorem", display (5) (p. 164), in the corrected form of Step 4 of the parent proof (erratum (vi): the printed measure estimate (5) is replaced by a Fubini–Tonelli bound L^{n+ℓ}({a ∈ B_{1/4}(q) : p_j(a) ∈ B_j}) ≤ L^{n+1}(B_j)·(measure of a fibre)). Here the fibres are bounded by the unit cube [0,1]^{ι∖J}, of measure 1, instead of an (ℓ−1)-dimensional ball; in the parent application ι = {1,…,n+ℓ}, J is the index set of S_j (|J| = n + 1), B = B_j, and B_{1/4}(q) ⊆ [0,1]^{n+ℓ}.

Notation: ι∖J := {i ∈ ι : i ∉ J}; Q := {a ∈ E_ι : 0 ≤ a_i ≤ 1 for all i ∈ ι}; S := {a ∈ Q : π_J(a) ∈ B}; ℝ^A carries the product Lebesgue measure λ_A := ⊗_{i∈A} L¹ (for A = ∅ this is the unit point mass).

1. Coordinates. The coordinate map E_ι → ℝ^ι, a ↦ (a_i)_{i∈ι}, is a measurable bijection with measurable inverse which carries L^ι to λ_ι (the Lebesgue measure of EuclideanSpace is the product measure in coordinates); likewise E_J → ℝ^J carries L^J to λ_J. The restriction map ℝ^ι → ℝ^J × ℝ^{ι∖J}, f ↦ (f|_J, f|_{ι∖J}), is a measurable bijection with measurable inverse carrying λ_ι to the product measure λ_J ⊗ λ_{ι∖J} (the product measure over ι splits into the products over J and over ι∖J). Let e : E_ι → ℝ^J × ℝ^{ι∖J} be the composite. Then e is a measure-preserving measurable bijection with measurable inverse, so L^ι(e⁻¹(Z)) = (λ_J ⊗ λ_{ι∖J})(Z) for every set Z (for a measurable equivalence this holds for arbitrary, not necessarily measurable, sets).
2. A rectangle containing S. Let B′ := {g ∈ ℝ^J : the point of E_J with coordinates g lies in B} and C := [0,1]^{ι∖J}. If a ∈ S, then e(a) = ((a_i)_{i∈J}, (a_i)_{i∈ι∖J}); here (a_i)_{i∈J} ∈ B′ because π_J(a) ∈ B, and (a_i)_{i∈ι∖J} ∈ C because a ∈ Q. Hence S ⊆ e⁻¹(B′ × C).
3. Fubini–Tonelli for a rectangle. For σ-finite measures ν₁, ν₂ the product measure satisfies (ν₁ ⊗ ν₂)(B′ × C) = ν₁(B′)·ν₂(C) for arbitrary sets B′, C. By monotonicity and step 1,
   L^ι(S) ≤ L^ι(e⁻¹(B′ × C)) = (λ_J ⊗ λ_{ι∖J})(B′ × C) = λ_J(B′)·λ_{ι∖J}(C).
4. The two factors. λ_{ι∖J}(C) = ∏_{i∈ι∖J} L¹([0,1]) = 1 (an empty product is 1). And λ_J(B′) = L^J(B), because B′ is the preimage of B under the measure-preserving measurable bijection ℝ^J → E_J of step 1.
5. Therefore L^ι(S) ≤ L^J(B)·1 = L^J(B). ∎

## Key steps

1. Identify E_ι with ℝ^J × ℝ^{ι∖J} by a measure-preserving measurable bijection e (coordinates, then splitting the product Lebesgue measure).
2. The set is contained in e⁻¹(B′ × [0,1]^{ι∖J}), B′ the coordinate copy of B.
3. Rectangle formula for product measures: L^ι(set) ≤ L^J(B′)·L^{ι∖J}([0,1]^{ι∖J}) = L^J(B)·1.

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d); git rev-parse HEAD = d8d46c9587747dee0751a1f780fcafdba16a3886; lake-manifest.json mathlib rev 25730c7c759d108ef87ab70af2342a196760f79d`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean workspace GMT/Ch06/Contract.lean; cmp GMT/Ch06/Submission.lean GMT/Ch06/Contract.lean (both byte-identical)`
- `python3 -I: verifier/gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') = [open MeasureTheory Filter Set Metric, open scoped ENNReal NNReal Topology, namespace GMT.Ch06, open Poincare.SimonGMT.Chapter06, open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasWeightedApproximateTangentSpaceAt), open Poincare.SimonGMT.Chapter01 (dimensionalUpperDensity), noncomputable section, end]`
- `rg -n 'theorem exists_disjoint_subfamily_covering_enlargement_closedBall' mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean (158; requires τ > 3, used with τ = 5)`
- `rg -n 'theorem exists_fiveTimesCovering' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityCovering.lean (26; Simon Ch. 1, 3.4, alternative to Mathlib's Vitali)`
- `rg -n 'volume_pi_closedBall' mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean (278: volume (closedBall a r) = ofReal ((2r)^card ι) in the sup metric)`
- `rg -n 'EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp|PiLp.volume_preserving_toLp' mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean (124, 139)`
- `rg -n 'theorem volume_preserving_piEquivPiSubtypeProd' mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean (726); rg -n 'theorem prod_prod ' mathlib/Mathlib/MeasureTheory/Measure/Prod.lean (231, arbitrary sets); rg -n 'theorem measure_preimage_equiv' mathlib/Mathlib/Dynamics/Ergodic/MeasurePreserving.lean (155)`
- `rg -n 'theorem countable_meas_pos_of_disjoint_iUnion ' mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean (305); rg -n 'theorem tsum_meas_le_meas_iUnion_of_disjoint ' mathlib/Mathlib/MeasureTheory/Measure/Basic.lean (167); rg -n 'theorem measure_biUnion_le |theorem measure_biUnion_finset_le ' mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean (74, 80)`
- `rg -n 'theorem infDist_lt_iff' mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean (513, needs s.Nonempty); rg -n 'theorem EuclideanSpace.dist_eq' mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean (158); rg -n 'theorem dist_apply_le' mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean (652); rg -n 'exists_subset_card_eq' mathlib/Mathlib/Data/Finset/Card.lean (677)`
- `rg -n -i 'vitali|5-times|five.times|covering' project/GMT (only Ch01 Besicovitch/Vitali-property statements and a Ch05 README pointer to Chapter01.exists_fiveTimesCovering; no periodic-tube maximal or cylinder Fubini lemma)`
- `rg -n 'dgc_tube_cover|dgc_periodic_maximal|dgc_cylinder_volume' project, lake-packages-25730c7c/simongmt/Poincare, mathlib/Mathlib (no match)`
- `python3 -I over dag.json (531 nodes): the three proposed lean_names vs all reservations (no collision); regex search of node statements for covering/Vitali/Fubini/maximal (no reusable node)`
- `sed -n '1640,1790p' book/chapter-06.txt (printed (1)–(7) of the proof of 5.1, pp. 163–164)`
- `python3 -I validate_lean_statement (verifier/lean_contract.py) on the three statements (all valid); lake env lean /tmp/goodcenter-a1-scratch/stmts/NC_<key>.lean for tube_cover, periodic_maximal, cylinder_volume (exit 0, only the expected sorry warning)`
- `lake env lean /tmp/goodcenter-a1-scratch/AllProofs.lean (full proofs of the three children and of Submission.deformation_good_center from them; no sorry; #print axioms = [propext, Classical.choice, Quot.sound] for all four)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter01/DensityCovering.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Dynamics/Ergodic/MeasurePreserving.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Finset/Card.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-good-center-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/goodcenter-a1-scratch/stmts/statements.json`
- `/tmp/goodcenter-a1-scratch/stmts/NC_tube_cover.lean`
- `/tmp/goodcenter-a1-scratch/stmts/NC_periodic_maximal.lean`
- `/tmp/goodcenter-a1-scratch/stmts/NC_cylinder_volume.lean`
- `/tmp/goodcenter-a1-scratch/AllProofs.lean`

Pinned revisions are confirmed. The frozen Contract equals the Submission and is byte-identical to the snapshot, and the selected frozen type equals the DAG entry.

Neither the project nor SimonGMT has a periodic-tube maximal inequality or a cylinder Fubini lemma, so the children are built on pinned Mathlib primitives:
- 5-times covering: Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall (τ = 5); SimonGMT's Chapter01.exists_fiveTimesCovering is an equivalent alternative.
- Countability of the subfamily and summation: Measure.countable_meas_pos_of_disjoint_iUnion, tsum_meas_le_meas_iUnion_of_disjoint and measure_biUnion_le.
- Ball volume bound (2r)^k: Real.volume_pi_closedBall together with EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp.
- Fubini for rectangles of arbitrary sets: volume_preserving_piEquivPiSubtypeProd, Measure.prod_prod and MeasurePreserving.measure_preimage_equiv.
- Tube step: infDist_lt_iff (needs La ≠ ∅, which follows from exists_subset_card_eq), EuclideanSpace.dist_eq and PiLp.dist_apply_le.

All three child types validate and elaborate in the exact comparator challenge scope. All three were fully proved in scratch, and Submission.deformation_good_center was kernel-checked from them with axioms [propext, Classical.choice, Quot.sound] and no sorry. No name collides with a DAG reservation or an existing declaration, and no existing node has a reusable identical statement. No Matrix/IsUnit construction occurs.
