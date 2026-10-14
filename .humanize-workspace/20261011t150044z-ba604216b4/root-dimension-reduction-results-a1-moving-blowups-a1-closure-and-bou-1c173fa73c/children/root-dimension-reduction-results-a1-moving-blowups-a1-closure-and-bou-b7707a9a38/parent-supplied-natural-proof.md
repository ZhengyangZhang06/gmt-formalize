# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.slice_limit-a1.slice_bound-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.slice_limit-a1.slice_bound-a1.boundary_slice-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Write S_h := W ∩ {t − h < f < t} and ℓ := liminf_{h→0+} ofReal(h⁻¹)·μ(S_h), the liminf taken along 𝓝[>]0 in [0, ∞]. The claim is boundaryMassOn(B, W) ≤ L·ℓ.
1. Case m = 0. For a 0-dimensional current, boundaryMassOn(B, W) = 0 by definition, and 0 ≤ L·ℓ in [0, ∞].
2. Case m = m' + 1. By definition boundaryMassOn(B, W) = M_W(∂B), where ∂B ∈ 𝒟_{m'}(U). Put Y := ∂T ∈ 𝒟_{m'+1}(U).
3. Representations. By hypothesis, Y(ω) = ∂T(ω) = ∫ ξ(x)(ω(x)) dμ(x) for every ω ∈ 𝒟^{m'+1}(U). Moreover ∂Y = ∂∂T = 0 (SimonGMT GeometricCurrentOn.boundary_boundary). Write 0 for both the zero measure on ℝ^P and the zero field ℝ^P → Λ_{m'}(ℝ^P). Then for every ζ ∈ 𝒟^{m'}(U), ∂Y(ζ) = 0 = ∫ 0(x)(ζ(x)) d0(x), because an integral with respect to the zero measure vanishes (Mathlib integral_zero_measure).
4. Hypotheses of (SL). Apply (SL) with k := m', the open set U, T := Y, (μ, ξ), (μ', ξ') := (0, 0), f and L. Its hypotheses hold:
- U is open.
- μ(K) < ∞ for every compact K ⊆ U, by hypothesis.
- The zero measure gives every set measure 0 < ∞.
- ξ is a.e. strongly measurable for μ, by hypothesis.
- Every function is a.e. strongly measurable for the zero measure (Mathlib aestronglyMeasurable_zero_measure), in particular the zero field.
- The bound |ξ(x)(α)| ≤ |α| holds for μ-a.e. x, by hypothesis.
- The bound for the zero field holds 0-a.e., because the almost-everywhere filter of the zero measure is ⊥ (Mathlib ae_zero), so every property holds 0-a.e.
- The two representation identities are those of step 3.
- f is L-Lipschitz.
5. Conclusions of (SL). There are families A'_s ∈ 𝒟_{m'+1}(U) and B'_s ∈ 𝒟_{m'}(U) (s ∈ ℝ) with:
(i) A'_s(ω) = ∫_{f<s} ξ(x)(ω(x)) dμ(x) for all s and all ω ∈ 𝒟^{m'+1}(U);
(ii) B'_s(ζ) = ∫_{f<s} 0(x)(ζ(x)) d0(x) for all s and all ζ ∈ 𝒟^{m'}(U);
(iii) M_{W'}(∂A'_s − B'_s) ≤ L·liminf_{h→0+} ofReal(h⁻¹)·μ(W' ∩ {s − h < f < s}) for every open W' and every s.
The two remaining conclusions of (SL) are not needed.
6. Identification at s = t. By (i) and the hypothesis on B, A'_t(ω) = ∫_{f<t} ξ(x)(ω(x)) dμ(x) = B(ω) for every ω ∈ 𝒟^{m'+1}(U). Currents are determined by their values (SimonGMT GeometricCurrentOn.ext), so A'_t = B. By (ii), B'_t(ζ) is an integral with respect to the restriction of the zero measure, which is the zero measure, so B'_t(ζ) = 0 = 0(ζ) for every ζ, and B'_t = 0 by ext. Finally, subtraction of currents is pointwise, so (∂B − 0)(ζ) = ∂B(ζ) − 0 = ∂B(ζ) for every ζ. Hence ∂A'_t − B'_t = ∂B − 0 = ∂B by ext.
7. Apply (iii) with W' := W, which is open by hypothesis, and s := t. This gives boundaryMassOn(B, W) = M_W(∂B) = M_W(∂A'_t − B'_t) ≤ L·liminf_{h→0+} ofReal(h⁻¹)·μ(W ∩ {t − h < f < t}) = L·ℓ. ∎

## Key steps

1. If m = 0, then boundaryMassOn(B, W) = 0 by definition.
2. If m = m' + 1, then (μ, ξ) represents ∂T and the zero measure with the zero field represents ∂∂T = 0. These satisfy all finiteness, measurability and a.e.-bound hypotheses of (SL).
3. (SL) applied to ∂T gives A', B' with A'_t = B and B'_t = 0 (GeometricCurrentOn.ext) and M_W(∂A'_t − B'_t) ≤ L·liminf h⁻¹μ(W ∩ {t−h<f<t}).
4. ∂A'_t − B'_t = ∂B, so boundaryMassOn(B, W) = M_W(∂B) satisfies the bound.

## Reference use

### local-project

Queries:
- `cat SNAP/manifest.json; git rev-parse HEAD; cmp GMT/Ch07/Submission.lean SNAP/project/GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean SNAP/project/GMT/Ch07/Contract.lean; python3 read of lake-manifest.json revs (mathlib, simongmt)`
- `python3 scans of RUN/dag.json: selected node (depth 5, decomposing, no children); lean_name collision check for dmcbr_sl_sb_massOn_eq_of_apply_eq_neg, dmcbr_sl_sb_ennreal_liminf_add_le, dmcbr_sl_sb_boundaryMassOn_slice_le (no match); twin nodes cmcsd_sh_slice_boundaryMassOn_le (byte-identical frozen type to the boundary_slice child, status decomposing) and cbrsl_slice_boundary_mass_bound (queued); short statements mentioning liminf, massOn or neg (no accepted generic lemma)`
- `grep -n '_existing_lean_name_problem|_reference_use_problem|max_depth' /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py and prompts.py`
- `rg/grep over SNAP/mathlib/Mathlib: le_liminf_add, liminf_add_le, biSup_add_biSup_le', limsup_eq_iInf_iSup (to_dual liminf_eq_iSup_iInf), aestronglyMeasurable_zero_measure, integral_zero_measure, ae_zero, tsupport_neg; grep liminf.*add in Topology/Instances/ENNReal/Lemmas.lean and Order/Filter/ENNReal.lean`
- `rg over SNAP/project for massOn_neg, liminf sum lemmas, dmcbr_sl_sb (no match)`
- `grep over .lake/packages/simongmt/Poincare for massOn_neg, massOn_sub, Neg instances on GeometricCurrentOn (no match); sed of Chapter06/Mass.lean (covectorEuclideanNorm, massAdmissibleOn, massOn, le_massOn) and Chapter06/Currents.lean (TestFormOn, GeometricCurrentOn, boundary, ext, boundary_boundary, zero_apply)`
- `grep -n -i slic book/chapter-06.txt; sed -n 1330,1400p (Simon Ch. 6 (4.6)-(4.10))`
- `lake env lean /tmp/dmcbr-sb-decomp/Probe.lean (#check of all used names) and /tmp/dmcbr-sb-decomp/Check.lean (three child proofs, exact frozen parent type from them, #print axioms); validate_lean_statement from verifier/lean_contract.py and runtime lean_contract.py on all four types`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/EReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Filter.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-1c173fa73c/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/prompts.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/dmcbr-sb-decomp/Probe.lean`
- `/tmp/dmcbr-sb-decomp/Check.lean`

Pins match. HEAD b4d606d is the snapshot project commit. Mathlib 25730c7c and SimonGMT 2b366308 match lake-manifest.json. Submission.lean and Contract.lean are byte-identical to the snapshot contract. The snapshot project has no mass-negation lemma, no ENNReal liminf-sum lemma and no dmcbr_sl_sb declaration. SimonGMT Chapter06 provides massOn_mono, le_massOn, covectorEuclideanNorm_neg, GeometricCurrentOn.ext, boundary_boundary and zero_apply, but no mass-under-negation lemma. Mathlib's le_liminf_add requires AddCommGroup. The EReal le_liminf_add and ENNReal.liminf_add_of_*_tendsto_zero do not give ℝ≥0∞ superadditivity, so liminf_add is derived from liminf_eq_iSup_iInf (to_dual of limsup_eq_iInf_iSup, Order/LiminfLimsup.lean:296) and ENNReal.biSup_add_biSup_le' (Basic/ENNReal/Operations.lean:674). The zero-representation step uses aestronglyMeasurable_zero_measure, integral_zero_measure and ae_zero. The three child names collide with no DAG node. The boundary_slice type is byte-identical to the unaccepted twin cmcsd_sh_slice_boundaryMassOn_le, so that name cannot be reused. All four types pass both validate_lean_statement implementations and elaborate in the contract scope. In /tmp/dmcbr-sb-decomp/Check.lean (sha256 efc82f98c106b99309b59da4cbe01b9195da6d79bad62e438977befb63e50dfe), all three children are proved and the exact frozen parent type is proved from them; #print axioms reports only propext, Classical.choice and Quot.sound.
