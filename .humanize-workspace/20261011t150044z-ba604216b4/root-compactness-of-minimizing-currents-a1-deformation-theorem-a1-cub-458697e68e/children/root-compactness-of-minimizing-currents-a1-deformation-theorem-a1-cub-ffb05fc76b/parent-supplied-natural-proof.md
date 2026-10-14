# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1.smooth_approx-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1.smooth_approx-a1.mollify_adjoint-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 2, 3(b)(i) and 3(d) of the parent proof. These are differentiation under the integral sign, the divergence formula div(φ̌_σ ⋆ g)(y) = −∫ Dφ_σ(x − y)(g(x)) dx, and the Fubini identity ∫ Du_σ(x)(g(x)) dx = −∫ ū · div(φ̌_σ ⋆ g). Here they are stated for an arbitrary C¹ compactly supported kernel η in place of φ_σ, and arbitrary integrable u, s in place of ū, g. In Simon this is the mollification computation of Ch. 2, 2.5 (book/chapter-02.txt lines 543–545).

Notation. P ∈ ℕ. ℝ^P := Euclid P = EuclideanSpace ℝ (Fin P) with Lebesgue measure (volume). |·| is the Euclidean norm, ‖·‖ the operator norm and D the Fréchet derivative (fderiv). div G(z) := trace DG(z), the LinearMap.trace of the linear map underlying fderiv. For a kernel k : ℝ^P → ℝ and a : ℝ^P → E (E = ℝ or ℝ^P), (k ⋆ a)(x) := ∫ k(t) a(x − t) dt. This is Mathlib's `convolution k a (ContinuousLinearMap.lsmul ℝ ℝ) volume x` (convolution_def, ContinuousLinearMap.lsmul_apply). η̌(z) := η(−z), which is `fun z => η (-z)` in the Lean statement. All integrals are Bochner integrals over ℝ^P.

Hypotheses: η : ℝ^P → ℝ is C¹ with compact support; u : ℝ^P → ℝ and s : ℝ^P → ℝ^P are integrable. Claim: ∫ D(η ⋆ u)(x)(s(x)) dx = −∫ u(z) div(η̌ ⋆ s)(z) dz.

1. Dη is continuous, compactly supported and bounded. η is C¹, so Dη is continuous (ContDiff.continuous_fderiv). Off the compact set tsupport η, η vanishes on an open set, so Dη = 0 there. Hence Dη has compact support (HasCompactSupport.fderiv). A continuous compactly supported function is bounded, so fix C with ‖Dη(y)‖ ≤ C for all y (Continuous.bounded_above_of_compact_support).

2. The reflected kernel. η̌ = η ∘ (−id) is C¹, being the composition with the linear map −id (ContDiff.comp contDiff_neg). It has compact support, since tsupport η̌ = −tsupport η (HasCompactSupport.comp_homeomorph with Homeomorph.neg). By the chain rule, Dη̌(y) = Dη(−y) ∘ (−id), i.e. Dη̌(y)h = −Dη(−y)h for all y, h (HasFDerivAt.comp with (hasFDerivAt_id y).neg, then HasFDerivAt.fderiv). As in step 1, Dη̌ is continuous with compact support.

3. Derivative of η ⋆ u. η is C¹ with compact support and u is locally integrable (being integrable). Differentiation under the integral sign therefore gives, for every x, that η ⋆ u is differentiable at x with D(η ⋆ u)(x) = (Dη ⋆ u)(x) = ∫ u(x − t) Dη(t) dt ∈ L(ℝ^P, ℝ). This is Mathlib's HasCompactSupport.hasFDerivAt_convolution_left; volume on Euclid P is add-left-invariant and neg-invariant. The substitution t = x − z (convolution_eq_swap) turns this into ∫ Dη(x − z) u(z) dz.

The integrand z ↦ u(z) Dη(x − z) is integrable: the convolution of the continuous compactly supported Dη with the locally integrable u exists (HasCompactSupport.convolutionExists_left, then ConvolutionExistsAt.integrable_swap). Evaluation at the fixed vector s(x) is a continuous linear map L(ℝ^P, ℝ) → ℝ, so it commutes with the integral (ContinuousLinearMap.integral_apply):
   D(η ⋆ u)(x)(s(x)) = ∫ Dη(x − z)(s(x)) u(z) dz   for every x.   (3.1)

4. Divergence of η̌ ⋆ s. Apply the reasoning of step 3 to the C¹ compactly supported kernel η̌ and the locally integrable s. For every z, D(η̌ ⋆ s)(z) = ∫ A_{z,x} dx in L(ℝ^P, ℝ^P). Here A_{z,x} is the rank-one map h ↦ (Dη̌(z − x)h) s(x) (in Mathlib, ContinuousLinearMap.precompL applied to lsmul), and x ↦ A_{z,x} is integrable.

The trace is a linear functional on the finite-dimensional space L(ℝ^P, ℝ^P), hence continuous. So it commutes with the integral (ContinuousLinearMap.integral_comp_comm, applied to LinearMap.toContinuousLinearMap of trace ∘ coercion). The trace of the rank-one map h ↦ a(h)w, for a ∈ L(ℝ^P, ℝ) and w ∈ ℝ^P, is a(w) (LinearMap.trace_smulRight). Hence, by step 2 and −(z − x) = x − z,
   div(η̌ ⋆ s)(z) = ∫ Dη̌(z − x)(s(x)) dx = −∫ Dη(x − z)(s(x)) dx   for every z.   (4.1)

5. Fubini. Let H(x, z) := Dη(x − z)(s(x)) · u(z) on ℝ^P × ℝ^P. H is a.e.-strongly measurable for the product measure: (x, z) ↦ Dη(x − z) is continuous, s ∘ fst and u ∘ snd are a.e.-strongly measurable, and evaluation and multiplication are continuous (ContinuousLinearMap.aestronglyMeasurable_comp₂, AEStronglyMeasurable.comp_fst, AEStronglyMeasurable.comp_snd, AEStronglyMeasurable.mul).

By step 1, |H(x, z)| ≤ ‖Dη(x − z)‖ |s(x)| |u(z)| ≤ C |s(x)| |u(z)|. The bound (x, z) ↦ C |s(x)| |u(z)| is integrable on the product because s and u are integrable (Integrable.mul_prod). Hence H is integrable (Integrable.mono'), and ∫_x ∫_z H(x, z) dz dx = ∫_z ∫_x H(x, z) dx dz (integral_integral_swap).

6. Conclusion. Combine (3.1), step 5, the factoring of the constant u(z) out of the inner integral (integral_const_mul) and (4.1):
   ∫ D(η ⋆ u)(x)(s(x)) dx = ∫_x ∫_z Dη(x − z)(s(x)) u(z) dz dx = ∫_z ∫_x Dη(x − z)(s(x)) u(z) dx dz = ∫_z u(z) (∫_x Dη(x − z)(s(x)) dx) dz = ∫_z u(z) (−div(η̌ ⋆ s)(z)) dz = −∫ u(z) div(η̌ ⋆ s)(z) dz (integral_neg). ∎
The case P = 0 needs no separate treatment.

Formalization note:
- The proof above is complete and is the one to formalize.
- For orientation only: the even-kernel special case (η̌ = η) is the comparator-accepted Submission.codim1_rdo_dg_sp_mollifier_adjoint of another DAG branch. That declaration is not in this node's proof base and must not be cited. Its Lean text, visible via `git show ae0277d4bed94a51b60fb4c7470fe259ed625e37:GMT/Ch07/Submission.lean` (lines 463–543), follows steps 1 and 3–6.
- It adapts to the present statement in two places: replace its oddness step by the chain rule of step 2, and in the last rewrite use Dη̌(z − x) = −Dη(x − z).
- The adapted proof compiles for the exact frozen statement with only `import GMT.Ch07.Submission`. It is about 95 lines, and its axioms are propext, Classical.choice and Quot.sound.

## Key steps

1. Dη is continuous, compactly supported and bounded by C; η̌ = η∘(−id) is C¹ with compact support and Dη̌(y) = −Dη(−y).
2. Differentiation under the integral sign: D(η⋆u)(x)(s(x)) = ∫ Dη(x − z)(s(x)) u(z) dz.
3. div(η̌⋆s)(z) = ∫ Dη̌(z − x)(s(x)) dx = −∫ Dη(x − z)(s(x)) dx, because the trace commutes with the integral and the trace of h ↦ a(h)w is a(w).
4. H(x,z) = Dη(x − z)(s(x))u(z) is dominated by C|s(x)||u(z)|, so Fubini applies.
5. Swapping the integrals and inserting the divergence formula gives −∫ u · div(η̌⋆s).

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); git -C .lake/packages/mathlib rev-parse HEAD = 25730c7c759d108ef87ab70af2342a196760f79d (= manifest.json mathlib_commit); git show 928be6d1df1e312edba524c8fd76720db6eee7eb:GMT/Ch07/Submission.lean (proof base = frozen contract)`
- `rg -n 'cmcdt_cbm_sa' project mathlib/Mathlib -g '*.lean' (no match); grep -c 'cmcdt_cbm_sa_' dag.json DAG.md dag.mmd issue-workers.json (0 each)`
- `rg -n -i 'mollif|convolution' project/GMT -g '*.lean' (no match)`
- `rg -n 'eLpNorm.*convolution|convolution.*eLpNorm|integral_norm_convolution|lintegral.*convolution|tendsto_convolution|convolution_tendsto' mathlib/Mathlib -g '*.lean'`
- `rg -n 'theorem dist_convolution_le |theorem support_convolution_subset_swap|theorem convolution_def|theorem ConvolutionExistsAt.integrable_swap|theorem AEStronglyMeasurable.convolution_integrand ' mathlib/Mathlib/Analysis/Convolution.lean`
- `rg -n 'HasCompactSupport.(hasFDerivAt_convolution_left|contDiff_convolution_left|convolutionExists_left|continuous_convolution_left)' mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean mathlib/Mathlib/Analysis/Convolution.lean`
- `rg -n 'theorem (normed_neg|support_normed_eq|integral_normed|contDiff_normed|hasCompactSupport_normed|continuous_normed|nonneg_normed)' mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `rg -n 'theorem Integrable.exists_hasCompactSupport_lintegral_sub_le' mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean; sed -n 1,80p mathlib/Mathlib/Analysis/Normed/Lp/SmoothApprox.lean`
- `rg -n 'theorem toDual_symm_apply' mathlib/Mathlib/Analysis/InnerProductSpace/Dual.lean; rg -n 'theorem norm_apply_le ' mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean; rg -n 'uniformContinuous_of_continuous' mathlib/Mathlib/Topology/UniformSpace/HeineCantor.lean; rg -n 'enorm_integral_le_lintegral_enorm|norm_integral_le_lintegral_norm' mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `python3 -I scan of runs/20261011T150044Z-ba604216b4/dag.json (1571 nodes) for mollif|convolution|ContDiffBump nodes; git show ae0277d4bed94a51b60fb4c7470fe259ed625e37:GMT/Ch07/Submission.lean (accepted even-kernel codim1_rdo_dg_sp_mollifier_adjoint, lines 463-543)`
- `lake env lean /tmp/sa-decomp/Avail.lean and /tmp/sa-decomp/Avail2.lean (import-closure check: convolution lemmas present; ContDiffBump.normed, Integrable.exists_hasCompactSupport_integral_sub_le and gradient absent; HasContDiffBump, IsNegInvariant, IsAddHaarMeasure and Regular instances resolve for volume on Euclid n)`
- `lake env lean /tmp/sa-decomp/final/TypesOnly.lean (four child types elaborate under import GMT.Ch07.Submission only); lake env lean /tmp/sa-decomp/final/Final.lean (all four children and the frozen parent proved; #print axioms: propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/SmoothApprox.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Dual.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/UniformSpace/HeineCantor.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-458697e68e/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-c373840d71/decomposition-v1.json`
- `/tmp/sa-decomp/final/TypesOnly.lean`
- `/tmp/sa-decomp/final/Final.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) matches the workspace Contract.lean and Submission.lean, and the proof base 928be6d1 is that pristine Submission.

Nothing in the snapshot proves any of the four obligations:
- the project GMT tree has no mollifier or convolution results;
- Mathlib has no L¹ convergence of mollifications (only the pointwise convolution_tendsto_right and Hölder-type eLpNorm bounds) and no mollifier adjoint identity.

Mathlib does supply every tool the child proofs cite:
- HasCompactSupport.hasFDerivAt_convolution_left, contDiff_convolution_left, convolutionExists_left and continuous_convolution_left;
- convolution_def, convolution_eq_swap, support_convolution_subset_swap, dist_convolution_le and AEStronglyMeasurable.convolution_integrand;
- ContDiffBump.normed and its lemmas;
- Integrable.exists_hasCompactSupport_lintegral_sub_le;
- InnerProductSpace.toDual_symm_apply, PiLp.norm_apply_le, HasCompactSupport.uniformContinuous_of_continuous and enorm_integral_le_lintegral_enorm.

Only two modules lie outside the frozen import closure: ContinuousMapDense (needed by mollify_l1) and BumpFunction.Normed (needed by the parent assembly). The child types elaborate without them.

The DAG's accepted even-kernel special case of mollify_adjoint (codim1_rdo_dg_sp_mollifier_adjoint, commit ae0277d4) lies on another branch outside the proof base. It served only as a proof template and is not reused. No cmcdt_cbm_sa_* name is reserved anywhere.

Complete Lean proofs of all four children, and of the exact frozen parent type from them, compile with standard axioms only (/tmp/sa-decomp/final/Final.lean).
