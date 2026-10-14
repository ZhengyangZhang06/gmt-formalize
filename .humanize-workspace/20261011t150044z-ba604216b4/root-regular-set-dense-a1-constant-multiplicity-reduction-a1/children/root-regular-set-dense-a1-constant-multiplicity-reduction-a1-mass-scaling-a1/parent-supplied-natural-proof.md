# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_dense-a1.constant_multiplicity_reduction-a1`
- Child DAG node: `root.regular_set_dense-a1.constant_multiplicity_reduction-a1.mass_scaling-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, step 5 (“For W ⊆ B, ι is a bijection from the forms admissible for M_W(T₀) (in 𝒟^n(B), spt ⊆ W, |ω| ≤ 1) onto those admissible for M_W(T), and T(ι(ω)) = N₀T₀(ω). Hence M_W(T) = N₀M_W(T₀).”), with N₀ replaced by an arbitrary real c ≥ 0. The same identity is used again in step 6(g) for S and S₀.

Notation. For a domain D write adm_D(W) := massAdmissibleOn D n W, so M_W(S) = sup{ofReal(S(ω)) : ω ∈ adm_D(W)} for S ∈ 𝒟_n(D). For ω' ∈ 𝒟^n(V), the form ι ω' ∈ 𝒟^n(U) has the same underlying differential form as ω', hence the same topological support and the same pointwise coefficient norms.

1. Every element of adm_U(W) comes from adm_V(W). Let ω ∈ adm_U(W). Then tsupport ω ⊆ W ⊆ V and ω is a test form, so ω' := (ω, its test-form property, tsupport ω ⊆ V) is an element of 𝒟^n(V). It lies in adm_V(W) (same support, same pointwise norms), and ι ω' = ω because the underlying forms agree (equality in the subtype).

2. ι maps adm_V(W) into adm_U(W): for ω' ∈ adm_V(W), the form ι ω' has tsupport ⊆ W and pointwise norms ≤ 1, since it is the same form.

3. Equality of the image sets. Since c ≥ 0, ofReal(c·t) = ofReal(c)·ofReal(t) for every real t (ENNReal.ofReal_mul). By steps 1 and 2 and the hypothesis T(ι ω') = c·T₀(ω'),
 {ofReal(T(ω)) : ω ∈ adm_U(W)} = {ofReal(T(ι ω')) : ω' ∈ adm_V(W)} = {ofReal(c)·ofReal(T₀(ω')) : ω' ∈ adm_V(W)}.

4. Pulling the constant out of the supremum. In [0, ∞], a·sup S = sup_{b∈S} a·b for every a and every set S (ENNReal.mul_sSup), and a supremum over an image set is the indexed supremum (sSup_image, iSup_image). Hence, by step 3,
 M_W(T) = sup_{ω'∈adm_V(W)} ofReal(c)·ofReal(T₀(ω')) = ofReal(c)·sup_{ω'∈adm_V(W)} ofReal(T₀(ω')) = ofReal(c)·M_W(T₀).
This is T.massOn W = ENNReal.ofReal c * T₀.massOn W. ∎

## Key steps

1. ι is a support- and norm-preserving bijection from adm_V(W) onto adm_U(W) when W ⊆ V (inverse: regard a form supported in W ⊆ V as a form in V).
2. T∘ι = c·T₀ and ofReal(c·t) = ofReal(c)·ofReal(t) for c ≥ 0 identify the two image sets.
3. ofReal(c) pulls out of the supremum in [0, ∞] (ENNReal.mul_sSup, sSup_image, iSup_image).

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
