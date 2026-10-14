# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_slice_tangent-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_slice_tangent-a1.slice_plane_algebra-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Step 1 (the description of S_t and of T_x), isolated as pure linear algebra for an arbitrary (not necessarily injective) continuous linear map L. Notation: ⟨·,·⟩ is the Euclidean inner product of ℝ^P (inner ℝ), and v ∈ (ℝ∙g)ᗮ iff ⟨g, v⟩ = 0 (Submodule.mem_orthogonal_singleton_iff_inner_right).

1. (a), direction g = 0 ⇒ ℓ = 0. Assume g = 0. For every e ∈ ℝ^m, ℓ(e) = ⟨g, L e⟩ = ⟨0, L e⟩ = 0. By extensionality of continuous linear maps, ℓ = 0.

2. (a), direction ℓ = 0 ⇒ g = 0. Assume ℓ = 0. Since g ∈ L(ℝ^m), choose w ∈ ℝ^m with L w = g. Then ⟨g, g⟩ = ⟨g, L w⟩ = ℓ(w) = 0, hence g = 0 (inner_self_eq_zero).

3. (b), inclusion ⊆. Let v ∈ L(ℝ^m) ∩ (ℝ∙g)ᗮ. Choose e ∈ ℝ^m with L e = v. Since v ∈ (ℝ∙g)ᗮ we have ⟨g, v⟩ = 0, so ℓ(e) = ⟨g, L e⟩ = ⟨g, v⟩ = 0. Thus e ∈ ker ℓ and v = L e ∈ L(ker ℓ) = Submodule.map L (ker ℓ).

4. (b), inclusion ⊇. Let v ∈ L(ker ℓ), i.e. v = L e with ℓ(e) = 0. Then v ∈ L(ℝ^m), and ⟨g, v⟩ = ⟨g, L e⟩ = ℓ(e) = 0, so v ∈ (ℝ∙g)ᗮ. Hence v ∈ L(ℝ^m) ∩ (ℝ∙g)ᗮ.

5. By steps 3 and 4 and submodule extensionality (ext v; the membership lemmas Submodule.mem_inf, LinearMap.mem_range, Submodule.mem_map, LinearMap.mem_ker, Submodule.mem_orthogonal_singleton_iff_inner_right, ContinuousLinearMap.coe_coe), LinearMap.range L ⊓ (ℝ ∙ g)ᗮ = Submodule.map L (LinearMap.ker ℓ). Together with steps 1–2 this proves (a) and (b). ∎

## Key steps

1. g = 0 ⇒ ℓ(e) = ⟨0, Le⟩ = 0 for all e.
2. ℓ = 0 and g = Lw ⇒ |g|² = ⟨g, Lw⟩ = ℓ(w) = 0.
3. v = Le ⊥ g ⟺ ℓ(e) = ⟨g, Le⟩ = 0, giving range L ∩ g^⊥ = L(ker ℓ) by double inclusion.

## Reference use

### local-project

Queries:
- `cat parent-child-handoff.json, parent-supplied-plan.md of node root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-f08a01d1b0; slice_family decomposition-v1.json (node ...-e999363692)`
- `python3 -I scan of dag.json: sibling nodes under slice_family-a1 (image_tangent frozen type), depth/status counts, regex 'implicit function|level set|implicitFunction|regular level|inverse function|toOpenPartialHomeomorph|Lindel' over statements, overlapping lean_statement scan ('ᗮ'+'Submodule.map', 'ker (fderiv', 'closedBall (c k)')`
- `grep -n 'def CountablyRectifiable|def HasApproximateTangentSpaceAt|theorem countablyRectifiable|theorem HasApproximateTangentSpaceAt' -r simongmt/Poincare/SimonGMT`
- `grep -rln 'implicitFunction|toOpenPartialHomeomorph|localInverse|implicit function|level set' simongmt/Poincare`
- `grep -rn 'theorem.*image.*le|euclideanHausdorffMeasure_image_le' simongmt/Poincare/SimonGMT`
- `ls mathlib/Mathlib/Analysis/Calculus/{Implicit.lean,ImplicitContDiff.lean,ImplicitFunction,InverseFunctionTheorem}; grep -n 'theorem|def' ImplicitContDiff.lean InverseFunctionTheorem/ContDiff.lean`
- `grep -rn 'μHE\[' and theorem list of mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean; grep hausdorffMeasure_image_le mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `grep coe_comp/toLinearMap_comp mathlib/Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Basic.lean`
- `#check probes in contract scope: MeasurableSet.image_of_continuousOn_injOn, ContDiffAt.toOpenPartialHomeomorph, OpenPartialHomeomorph.contDiffAt_symm, OpenPartialHomeomorph.hasFDerivAt_symm, OpenPartialHomeomorph.restrOpen, ContinuousLinearEquiv.isOpen, ContinuousLinearMap.prodₗᵢ, LinearMap.exists_extend, LinearEquiv.ofFinrankEq, TopologicalSpace.isOpen_iUnion_countable, ball_subset_interior_closedBall, countablyRectifiable_image_contDiffOn_open, euclideanHausdorffMeasure_image_le_of_lipschitzOn, EuclideanSpace.euclideanHausdorffMeasure_eq_volume, ae_restrict_iff', ae_all_iff`
- `git for-each-ref refs/heads | xargs git grep -l dor_lmbsf_pst (no match); survey of extra imports added to Submission.lean in proof branches`
- `python3 -I verifier lean_contract.validate_lean_statement + gmt-compare.child_modules(contract mode) on the 4 child statements; lake env lean on generated challenge modules and on /tmp/pst-decomp/{Assembly,Children,IFT,All}.lean with #print axioms`
- `book: sed chapter-06.txt 1150-1185 (Lemma 4.1), chapter-03.txt 20-60 (Lemma 1.2), 100-140 (Theorem 1.6), 437-445 (2.10), chapter-02.txt 1470-1495 (IFT remark, 6.4)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-f08a01d1b0/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-e999363692/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/ConstancyNormalCharts.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ImplicitContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/pst-decomp/All.lean`

Snapshot: project b4d606d, mathlib 25730c7c, simongmt 2b36630. No existing declaration states a regular-level-set chart (implicit function theorem), a countable chart cover, or the patch tangent-plane transfer. SimonGMT has no implicit-function or level-set chart lemma; Chapter08/ConstancyNormalCharts only does local inverses of normal coordinates.

No DAG node or branch uses dor_lmbsf_pst_* and no node has an overlapping statement, so all 4 children get fresh names.

Reusable library facts for the child proofs:
- Mathlib inverse function theorem: ContDiffAt.toOpenPartialHomeomorph, OpenPartialHomeomorph.contDiffAt_symm, OpenPartialHomeomorph.hasFDerivAt_symm and restrOpen. These need import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff, which is built.
- ContinuousLinearEquiv.isOpen, LinearMap.exists_extend, LinearEquiv.ofFinrankEq, TopologicalSpace.isOpen_iUnion_countable.
- Lusin–Souslin: MeasurableSet.image_of_continuousOn_injOn.
- SimonGMT Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn, reachable from Submission.
- EuclideanSpace.euclideanHausdorffMeasure_eq_volume.
- Chapter03.countablyRectifiable_image_contDiffOn_open (import Poincare.SimonGMT.Chapter03.SubmanifoldCover, built) and countablyRectifiable_iUnion.

Lean checks:
- All 4 child types pass validate_lean_statement and elaborate in the exact comparator scope.
- All 4 children have complete scratch proofs depending only on propext, Classical.choice and Quot.sound.
- The exact frozen parent type is proved from the children plus the sibling dor_lmbsf_c1_image_approxTangent; its only sorryAx is the stub for that sibling (/tmp/pst-decomp/All.lean).
