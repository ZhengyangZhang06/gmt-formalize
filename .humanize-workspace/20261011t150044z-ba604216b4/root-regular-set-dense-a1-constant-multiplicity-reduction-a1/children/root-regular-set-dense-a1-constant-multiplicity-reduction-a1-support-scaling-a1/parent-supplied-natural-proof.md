# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_dense-a1.constant_multiplicity_reduction-a1`
- Child DAG node: `root.regular_set_dense-a1.constant_multiplicity_reduction-a1.support_scaling-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 4(a) (spt T₀ ⊆ spt T, using W' := W ∩ B_s(y)) and step 4(b) (z₀ ∈ spt T₀, by regarding forms supported in W' ⊆ B as forms in B), stated for an arbitrary open V ⊆ U and an arbitrary nonzero real scale c.

1. Reduction. Since V ⊆ U, spt T ∩ V = (U ∖ Z(T)) ∩ V = V ∖ Z(T), while spt T₀ = V ∖ Z(T₀). So it suffices to prove, for every y ∈ V: y ∈ Z(T₀) ⇔ y ∈ Z(T).

2. Z(T₀) ⊆ Z(T). Let y ∈ W', where W' is open, closure(W') is compact, closure(W') ⊆ V and T₀(ω') = 0 for every ω' ∈ 𝒟^n(V) with tsupport ω' ⊆ W'. Then closure(W') ⊆ V ⊆ U. Let ω ∈ 𝒟^n(U) with tsupport ω ⊆ W'. Then tsupport ω ⊆ W' ⊆ closure(W') ⊆ V, so ω' := (ω regarded as a test form in V) ∈ 𝒟^n(V), ι ω' = ω (same underlying form) and tsupport ω' ⊆ W'. Hence T(ω) = T(ι ω') = c·T₀(ω') = c·0 = 0. So W' is one of the sets whose union is Z(T), and y ∈ Z(T).

3. Z(T) ∩ V ⊆ Z(T₀). Let y ∈ V and y ∈ W, where W is open, closure(W) is compact, closure(W) ⊆ U and T vanishes on all ω ∈ 𝒟^n(U) with tsupport ω ⊆ W. As V is open, choose s > 0 with B_s(y) ⊆ V, and put W' := W ∩ B_{s/2}(y).
 (a) W' is open and y ∈ W'.
 (b) closure(W') ⊆ closure(B_{s/2}(y)) ⊆ B̄_{s/2}(y) ⊆ B_s(y) ⊆ V.
 (c) closure(W') ⊆ closure(W), so closure(W') is a closed subset of the compact set closure(W), hence compact.
 (d) If ω' ∈ 𝒟^n(V) with tsupport ω' ⊆ W', then tsupport(ι ω') = tsupport ω' ⊆ W, so c·T₀(ω') = T(ι ω') = 0, and T₀(ω') = 0 because c ≠ 0.
 By (a)-(d), W' is one of the sets whose union is Z(T₀), so y ∈ Z(T₀).

4. By steps 1-3, spt T₀ = V ∖ Z(T₀) = V ∖ Z(T) = spt T ∩ V. ∎

## Key steps

1. spt T ∩ V = V ∖ Z(T) and spt T₀ = V ∖ Z(T₀), so compare the zero regions at points of V.
2. A zero set W' of T₀ (closure compact in V) is a zero set of T: forms in U supported in W' are ι of forms in V and T = c·T₀ there.
3. A zero set W of T through y ∈ V shrinks to W ∩ B_{s/2}(y) with closure compact in V, on which T₀ = c⁻¹·T∘ι vanishes (c ≠ 0).

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `python3 over dag.json: lean_name/lean_statement of all 111 nodes; frozen statements of rsd_massOn_eq_measure, rsd_mem_support_iff_measure_ball_pos, rsd_isIntegerMultiplicity_int_combination and of the selected node; rg -l rsd_cmr_ over the run directory and GMT/`
- `python3 over nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1/decomposition-v1.json (convention: children do not use the parent's resolved siblings)`
- `rg -n 'restrictDomain|zeroRegion|VanishesOn|theorem .*massOn|theorem .*support' simongmt/Poincare/SimonGMT (Chapter06)`
- `sed simongmt Chapter06/{Currents,Mass,CurrentLocalEquality,Forms}.lean and Chapter03/Rectifiable.lean (HasApproximateTangentSpaceAt, blowUpMap, CountablyRectifiable.mono)`
- `grep/rg in local-references/123e8435b4a2469b/mathlib: exists_contDiff_support_eq_eq_one_iff, IsCompact.exists_cthickening_subset_open, measure_null_of_locally_null, ae_withDensity_iff, setIntegral_eq_of_subset_of_*, euclideanHausdorffMeasure_homothety_image, LipschitzWith.hausdorffMeasure_image_le, ENNReal.mul_sSup`
- `lake env lean /tmp/rsd-cmr-decomp/build/FinalChildren.lean, FinalAssembly.lean, FinalSiblings.lean, FinalLeaves.lean (#print axioms)`
- `book: chapter-05.txt proof of 7.3; chapter-06.txt 2.11, 2.16, 3.1, 3.2; chapter-03.txt 1.4-1.6`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-constant-multiplicity-reduction-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-05.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/rsd-cmr-decomp/build/FinalChildren.lean`
- `/tmp/rsd-cmr-decomp/build/FinalAssembly.lean`
- `/tmp/rsd-cmr-decomp/build/FinalSiblings.lean`
- `/tmp/rsd-cmr-decomp/build/FinalLeaves.lean`

The snapshot contract (project b4d606d, Mathlib 25730c7c) is byte-identical to the workspace Contract.lean and Submission.lean.

The pinned library proves none of the children:
- Chapter06 has restrictDomain, testFormOnInclusion, zeroRegion/support, massOn_mono and le_massOn, but no mass or support lemma for restricted or scaled currents.
- Currents.lean explicitly leaves the integral continuity estimate (IMRep action as a current) open.
- Chapter03 has HasApproximateTangentSpaceAt and CountablyRectifiable.mono, but no locality or null-set invariance of approximate tangent spaces.

Reusable tools, all used in compiled proofs:
- Mathlib: exists_contDiff_support_eq_eq_one_iff, IsCompact.exists_cthickening_subset_open, measure_null_of_locally_null, ae_withDensity_iff, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero, setIntegral_congr_set/_ae, ENNReal.mul_sSup.
- The muHE scaling and isometry lemmas are cited for imrep_restrict.

Lean checks:
- All nine child types elaborate in the comparator scope.
- The conditional assembly of the exact frozen parent type from seven children plus the three frozen uncle types depends only on propext, Classical.choice and Quot.sound.
- Both sibling dependencies are verified.
- Five leaf children are fully proved.

No rsd_cmr_ name collides with the 111 live DAG declarations.
