# Parent-supplied natural-language proof

- Parent DAG node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.image_representation-a1.image_imrep-a1`
- Child DAG node: `root.minimizing_implies_stationary-a1.diffeo_pushforward-a1.image_representation-a1.image_imrep-a1.image_measure_comparison-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2 and 3 of the parent-supplied proof of dpfir_bilipschitz_image_imrep_exists, which follows Simon Ch. 6, 3.6-3.9. For injective maps this comparison replaces the area-formula step (book/chapter-06.txt lines 809-822; "by the area formula" at line 816). The Lipschitz image bound in step 5 is Simon Ch. 2, Theorem 1.8(i) (book/chapter-02.txt lines 270-276; proof lines 281-295). Lines 294-295 note that this part needs no measurability of the set. See also Federer, Geometric Measure Theory, 2.10.11, and Evans-Gariepy, Measure Theory and Fine Properties of Functions, §2.4.1, Theorem 1 (Theorem 2.8 in the 2015 revised edition).
Notation:
- E := ℝ^P (Euclid P) with its Borel σ-algebra, and H^n := μHE[n];
- for T ⊆ E, H^n⌞T := μHE[n].restrict T;
- for a measure ν and a measurable map ψ, ψ_#ν := ν.map ψ, so (ψ_#ν)(B) = ν(ψ^{-1}(B)) for Borel B.
All values lie in [0, ∞], with 0·∞ = 0. Λ^n means (Λ : [0, ∞])^n for the natural number n.
Hypotheses: Λ ≥ 0, φ : E → E is Λ-Lipschitz, ψ : E → E is Borel measurable, and ψ(φ(x)) = x for every x ∈ E. S ⊆ E is an arbitrary set.
1. Reduction to Borel test sets. For measures μ₁, μ₂ on E, μ₁ ≤ μ₂ iff μ₁(A) ≤ μ₂(A) for every Borel set A (Measure.le_iff). Fix a Borel set A ⊆ E. It suffices to show (ψ_#(H^n⌞φ(S)))(A) ≤ (Λ^n·(H^n⌞S))(A).
2. The left side. Since ψ is measurable and A is Borel, ψ^{-1}(A) is Borel.
- The image-measure formula (Measure.map_apply, using only Measurable ψ and MeasurableSet A) gives (ψ_#(H^n⌞φ(S)))(A) = (H^n⌞φ(S))(ψ^{-1}(A)).
- The restriction formula (μ⌞T)(B) = μ(B ∩ T) holds for every Borel B and every set T; Measure.restrict_apply needs only the evaluated set B to be measurable. With B = ψ^{-1}(A) and T = φ(S), (H^n⌞φ(S))(ψ^{-1}(A)) = H^n(ψ^{-1}(A) ∩ φ(S)).
No measurability of S or of φ(S) is used.
3. The right side. By the definition of the scalar multiple of a measure (Measure.smul_apply, then smul_eq_mul in [0, ∞]), (Λ^n·(H^n⌞S))(A) = Λ^n·(H^n⌞S)(A). Since A is Borel, Measure.restrict_apply gives (H^n⌞S)(A) = H^n(A ∩ S). So the right side equals Λ^n·H^n(A ∩ S).
4. The set identity ψ^{-1}(A) ∩ φ(S) = φ(A ∩ S).
(⊆) Let y ∈ ψ^{-1}(A) ∩ φ(S), and choose x ∈ S with y = φ(x). Then x = ψ(φ(x)) = ψ(y) ∈ A. So x ∈ A ∩ S and y = φ(x) ∈ φ(A ∩ S).
(⊇) Let y = φ(x) with x ∈ A and x ∈ S. Then ψ(y) = ψ(φ(x)) = x ∈ A, so y ∈ ψ^{-1}(A). Also y ∈ φ(S), because x ∈ S.
5. The Lipschitz image estimate. Put B := A ∩ S. Since φ is Λ-Lipschitz on E, it is Λ-Lipschitz on B (LipschitzWith.lipschitzOnWith). Hence H^n(φ(B)) ≤ Λ^n·H^n(B).
- This is the pinned theorem Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n (hφ.lipschitzOnWith). It states μHE[n] (f '' B) ≤ (K : ℝ≥0∞)^n * μHE[n] B whenever f is K-Lipschitz on B. It assumes nothing about measurability of B, and holds for every K ≥ 0 and n ∈ ℕ (including Λ = 0 and n = 0).
- Mathematically: let B ⊆ ⋃_j C_j with diam C_j < δ. Then φ(B) ⊆ ⋃_j φ(C_j) and diam φ(C_j) ≤ Λ·diam C_j < (Λ + 1)δ. So the size-(Λ+1)δ Hausdorff pre-measure of φ(B) is at most Λ^n times the size-δ pre-measure of B. Taking the infimum over covers and letting δ ↓ 0 gives the bound for μH[n]. The normalizing constant of μHE[n] multiplies both sides.
6. Conclusion. Combining steps 2, 4, 5 and 3:
(ψ_#(H^n⌞φ(S)))(A) = H^n(ψ^{-1}(A) ∩ φ(S)) = H^n(φ(A ∩ S)) ≤ Λ^n·H^n(A ∩ S) = (Λ^n·(H^n⌞S))(A).
Since A was an arbitrary Borel set, step 1 gives ψ_#(H^n⌞φ(S)) ≤ Λ^n·(H^n⌞S), that is, (μHE[n].restrict (φ '' S)).map ψ ≤ ((Λ : ℝ≥0∞) ^ n) • μHE[n].restrict S. ∎

## Key steps

1. Reduce ψ_#(H^n⌞φ(S)) ≤ Λ^n·(H^n⌞S) to Borel test sets A (Measure.le_iff).
2. Since ψ^{-1}(A) is Borel, Measure.map_apply and Measure.restrict_apply give ψ_#(H^n⌞φ(S))(A) = H^n(ψ^{-1}(A) ∩ φ(S)), with no measurability of S. Likewise Measure.smul_apply and Measure.restrict_apply give (Λ^n·H^n⌞S)(A) = Λ^n·H^n(A ∩ S).
3. ψ∘φ = id gives the set identity ψ^{-1}(A) ∩ φ(S) = φ(A ∩ S).
4. The Lipschitz image bound H^n(φ(A ∩ S)) ≤ Λ^n·H^n(A ∩ S) closes the chain. This is euclideanHausdorffMeasure_image_le_of_lipschitzOn (Simon Ch. 2, Thm 1.8(i)), valid for arbitrary sets.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json (project b4d606db, mathlib 25730c7c)`
- `python3 -I: read nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-image-rep-deb5dda114/{parent-child-handoff.json,decomposition-v1.json,decomposition-audit-v1.json,decomposition-review-receipt-v1.json,decomposition-scope-v1.json}`
- `python3 -I: dag.json scan of lean_name/lean_statement with regex (rectifiable|bilipschitz|hausdorffMeasure_image|image_le|restrict.*map|quasi|lipschitz_image|image_of_lipschitz), plus exact-membership check for dpfir_ii_map_restrict_image_le_smul and dpfir_ii_countablyRectifiable_image_of_lipschitz (free; 0 substring hits)`
- `python3 -I: issue-workers.json entries for image_imrep-a1 (attempt-1 worker never completed)`
- `git show <branch>:GMT/Ch07/Submission.lean | grep 'dpfir_ii|theorem Submission.' on the deb5dda114, 89b1ce4202, 0e98a44316, ddc9727a9c and 1f29e7d629 image-rep branches`
- `grep -n 'def CountablyRectifiable' and lemma list in simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -rn "CountablyRectifiable n (.* '' |CountablyRectifiable.image|countablyRectifiable_image|rectifiable_image" simongmt/Poincare local-references/123e8435b4a2469b/project/GMT`
- `grep -rln '.map ψ ≤|map_restrict_image|restrict_image.*le_smul' simongmt/Poincare local-references/123e8435b4a2469b/project/GMT (no match)`
- `grep -rn 'theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn' simongmt/Poincare/SimonGMT`
- `rg -n 'μHE\[' mathlib/Mathlib`
- `rg -n 'theorem le_iff|theorem absolutelyContinuous_of_le_smul|theorem comp_quasiMeasurePreserving|theorem lintegral_map \(|theorem lintegral_mono'|theorem lintegral_smul_measure|theorem to_rightInverse|theorem image_eq_preimage_of_inverse|theorem restrict_apply \(|theorem map_apply \(' mathlib/Mathlib`
- `grep -n measurable_from_nat mathlib/Mathlib/MeasureTheory/MeasurableSpace/*.lean`
- `python3 -I: verifier/gmt-compare.py contract_scope(GMT/Ch07/Contract.lean, GMT.Ch07.main_theorem)`
- `python3 -I: verifier/lean_contract.py validate_lean_statement on both child types (OK, unchanged)`
- `grep -n on book/chapter-02.txt, chapter-03.txt, chapter-06.txt for cited lines (816, 826-827, 270-295, 13-17, 52)`
- `lake env lean /tmp/dpfir-a2-scratch/Types.lean`
- `lake env lean /tmp/dpfir-a2-scratch/EndToEnd.lean (#print axioms on both children and the parent)`
- `lake env lean /tmp/dpfir-a2-scratch/Comparator.lean (#print axioms on the comparator targets)`
- `lake env lean /tmp/dpfir-a2-scratch/Inst.lean (constants used by the child-1 type)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-image-rep-deb5dda114/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-image-rep-deb5dda114/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-image-rep-deb5dda114/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-image-rep-deb5dda114/decomposition-scope-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/issue-workers.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/CompleteLattice.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/AbsolutelyContinuous.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/QuasiMeasurePreserving.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Antilipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Image.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/dpfir-a2-scratch/Types.lean`
- `/tmp/dpfir-a2-scratch/EndToEnd.lean`
- `/tmp/dpfir-a2-scratch/Comparator.lean`
- `/tmp/dpfir-a2-scratch/Inst.lean`

The pinned snapshot (project b4d606db, mathlib 25730c7c) proves neither child nor the parent. project/GMT has no dpfir_ii_ declarations, no Lipschitz-image rectifiability lemma and no map/restrict comparison. SimonGMT Chapter03 has only CountablyRectifiable.mono, countablyRectifiable_of_measure_zero, countablyRectifiable_range, countablyRectifiable_iUnion and the C¹-on-open-domain countablyRectifiable_image_contDiffOn_open; none of these is the Lipschitz-image statement.

Every library fact the child and parent proofs use exists at the pinned revisions:
- euclideanHausdorffMeasure_image_le_of_lipschitzOn (Chapter02/Lipschitz.lean:216, arbitrary sets);
- Measure.le_iff, map_apply, restrict_apply and smul_apply;
- Measure.absolutelyContinuous_of_le_smul;
- AEStronglyMeasurable.comp_quasiMeasurePreserving and QuasiMeasurePreserving.ae;
- lintegral_map, lintegral_mono' and lintegral_smul_measure;
- AntilipschitzWith.to_rightInverse, Set.image_eq_preimage_of_inverse and measurable_from_nat.
CountablyRectifiable (an H^n-null M₀ plus ℕ-indexed Lipschitz maps ℝ^n → E covering M) matches child 2's proof exactly.

The DAG (684 nodes) reserves neither proposed name. No node concludes CountablyRectifiable n (φ '' M) or a map/restrict comparison. The related accepted node dpf_itt_bilipschitz_image_locfin has a different type and is not reused.

In Lean, both child types elaborate in the comparator's replayed scope and pass validate_lean_statement. The ℝ≥0∞ action on measures is Measure.instSMul. Complete proofs of both children, and of the exact frozen parent type from them, compile using only propext, Classical.choice and Quot.sound.
