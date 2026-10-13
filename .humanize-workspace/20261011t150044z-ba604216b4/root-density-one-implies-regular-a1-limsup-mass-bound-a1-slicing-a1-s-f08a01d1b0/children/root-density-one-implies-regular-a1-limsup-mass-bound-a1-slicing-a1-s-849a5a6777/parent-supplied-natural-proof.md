# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_slice_tangent-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_slice_tangent-a1.level_set_chart_cover-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Step 2, last two sentences (“Γ_t is second countable, so there are countably many such data … with Γ_t = ⋃_k Λ_k(B_{ρ_k}(z_k)). If Γ_t = ∅ …”), made precise with the open neighbourhoods N supplied by the sibling level_set_local_chart (Lean dor_lmbsf_pst_level_set_local_chart). Notation: Γ := {y ∈ W : DF(y) ≠ 0 and F(y) = t}.

1. Case Γ = ∅. Take D_k := ∅, Λ_k := 0, c_k := 0 and ρ_k := −1 for all k. Then D_k is open, every map is C¹ on ∅ and injective on ∅, the properties required for z ∈ D_k are vacuous, B̄_{−1}(0) = ∅ ⊆ D_k (closedBall_eq_empty, as −1 < 0), and the covering property is vacuous because no y ∈ W satisfies DF(y) ≠ 0 and F(y) = t.

2. Case Γ ≠ ∅: local charts. For each y ∈ Γ apply level_set_local_chart to (n, W, F, y₀ := y); its hypotheses hold since W is open, F is C¹, y ∈ W and DF(y) ≠ 0. Choose the resulting data (D_y, Λ_y, c_y, ρ_y, N_y). Since F(y) = t, its conclusions read: D_y is open, Λ_y is C¹ and injective on D_y, and for z ∈ D_y, Λ_y(z) ∈ W, F(Λ_y(z)) = F(y) = t, DΛ_y(z) is injective and DΛ_y(z)(ℝⁿ) = ker DF(Λ_y(z)); B̄_{ρ_y}(c_y) ⊆ D_y; N_y is open with y ∈ N_y; and N_y ∩ F⁻¹(t) ⊆ Λ_y(B_{ρ_y}(c_y)).

3. Countable subfamily. The family (N_y)_{y∈Γ} consists of open sets in the second countable space ℝ^{n+1}, so there is a countable T ⊆ Γ with ⋃_{y∈T} N_y = ⋃_{y∈Γ} N_y (TopologicalSpace.isOpen_iUnion_countable). T is nonempty: pick y ∈ Γ; then y ∈ N_y ⊆ ⋃_{y'∈T} N_{y'}, so some y' lies in T. Hence T = {e(k) : k ∈ ℕ} for some sequence e : ℕ → Γ (Set.Countable.exists_eq_range).

4. Definition of the sequence. Put D_k := D_{e(k)}, Λ_k := Λ_{e(k)}, c_k := c_{e(k)}, ρ_k := ρ_{e(k)}. Openness of D_k, C¹-ness and injectivity of Λ_k on D_k, the four properties at z ∈ D_k (with F(Λ_k(z)) = F(e(k)) = t) and B̄_{ρ_k}(c_k) ⊆ D_k are the conclusions of step 2 for the point e(k).

5. Covering. Let y ∈ W with DF(y) ≠ 0 and F(y) = t. Then y ∈ Γ and y ∈ N_y ⊆ ⋃_{y'∈Γ} N_{y'} = ⋃_{y'∈T} N_{y'}, so y ∈ N_{e(k)} for some k. As F(y) = t = F(e(k)), y ∈ N_{e(k)} ∩ F⁻¹(F(e(k))) ⊆ Λ_k(B_{ρ_k}(c_k)) by step 2; i.e. y = Λ_k(z) for some z ∈ B_{ρ_k}(c_k). ∎

## Key steps

1. Empty regular level set: use empty charts with ρ_k = −1.
2. Otherwise apply level_set_local_chart at every regular point y, getting (D_y, Λ_y, c_y, ρ_y, N_y).
3. Second countability (Lindelöf) gives a countable subfamily of the N_y covering Γ; enumerate it by ℕ.
4. A regular point y with F(y) = t lies in some N_{e(k)} ∩ F⁻¹(t) ⊆ Λ_k(B_{ρ_k}(c_k)).

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
