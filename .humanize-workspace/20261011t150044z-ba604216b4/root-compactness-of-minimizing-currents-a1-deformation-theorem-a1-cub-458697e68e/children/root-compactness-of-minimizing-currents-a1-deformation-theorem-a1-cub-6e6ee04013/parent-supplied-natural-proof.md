# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1.smooth_approx-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1.smooth_approx-a1.grad_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 3 of the parent proof, the gradient bound by duality with the smoothed unit field. It is written with Mathlib's convolution order: the parent's field g̃ = φ̌_σ ⋆ g is here G = ρ̌ ⋆ s with ρ̌(z) := ρ(−z). In Simon this is the mollification fact Ch. 2, 2.5 (book/chapter-02.txt lines 543–545) as used in the proof of Ch. 2, 2.7 (lines 651–661).

Notation. m ∈ ℕ and n := m + 1. ℝⁿ means Euclid n = EuclideanSpace ℝ (Fin n) with its Lebesgue measure (volume); y_i is the i-th coordinate (Lean `y i`, i.e. `y.ofLp i`), |y| the Euclidean norm, ‖·‖ the operator norm and D the Fréchet derivative (fderiv). Q₁ := {y : 0 < y_i < 1 for all i}; for δ ∈ ℝ, Q_δ := {y : δ < y_i < 1 − δ for all i}; B_σ(0) is the open ball. div G(x) := trace DG(x) (LinearMap.trace of the linear map underlying fderiv). For a kernel k : ℝⁿ → ℝ and a : ℝⁿ → E (E = ℝ or ℝⁿ), (k ⋆ a)(x) := ∫ k(t) a(x − t) dt; this is Mathlib's `convolution k a (ContinuousLinearMap.lsmul ℝ ℝ) volume x` (convolution_def, ContinuousLinearMap.lsmul_apply). Integrals over a set are Bochner integrals for the restricted measure. "hyp(u, V)" abbreviates: ∫_{Q₁} u · div g ≤ V for every C^∞ (ContDiff ℝ (⊤ : ℕ∞)) map g : ℝⁿ → ℝⁿ with compact support, tsupport g ⊆ Q₁ and |g(y)| ≤ 1 for all y.

Hypotheses:
- u : ℝⁿ → ℝ is integrable on Q₁, and hyp(u, V) holds.
- 0 < σ < δ.
- ρ : ℝⁿ → ℝ is C^∞, ρ ≥ 0, ∫ρ = 1 and support ρ ⊆ B_σ(0).
Put ū := 1_{Q₁} u and f := ρ ⋆ ū. Claim: ∫_{Q_δ} ‖Df(x)‖ dx ≤ V.

This proof uses two sibling lemmas:
- smoothed_field (Submission.cmcdt_cbm_sa_smoothed_field): if 0 < σ < δ, k : ℝⁿ → ℝ is C^∞ with k ≥ 0, ∫k = 1 and support k ⊆ B_σ(0), and s is a.e.-strongly measurable with |s| ≤ 1 and s = 0 off Q_δ, then k ⋆ s is C^∞, has compact support, has tsupport in Q₁, and has norm ≤ 1 everywhere.
- mollify_adjoint (Submission.cmcdt_cbm_sa_mollify_adjoint): if η is C¹ with compact support and u', s are integrable, then ∫ D(η ⋆ u')(x)(s(x)) dx = −∫ u'(z) div(η̌ ⋆ s)(z) dz, where η̌(z) = η(−z).

0. Preliminaries.
 (a) δ > σ > 0.
 (b) Q₁ and Q_δ are measurable. Each is the finite intersection over i of {y : a < y_i} ∩ {y : y_i < b}, and y ↦ y_i is continuous (EuclideanSpace.proj; measurableSet_lt).
 (c) Q_δ ⊆ Q₁, since δ > 0 gives 0 < δ < y_i and y_i < 1 − δ < 1.
 (d) vol(Q_δ) ≤ vol(Q₁) < ∞. For y ∈ Q₁, |y|² = Σ_i y_i² ≤ n (EuclideanSpace.norm_eq), so Q₁ ⊆ closedBall(0, √n), which has finite measure (measure_closedBall_lt_top).
 (e) ū is integrable on ℝⁿ (integrable_indicator_iff with (b)).
 (f) ρ has compact support, because support ρ ⊆ B_σ(0) ⊆ closedBall(0, σ), which is compact (HasCompactSupport.intro). ρ is C¹, since C^∞ implies C¹ (ContDiff.of_le).

1. f is C^∞. ρ is C^∞ with compact support and ū is locally integrable, so f = ρ ⋆ ū is C^∞ (HasCompactSupport.contDiff_convolution_left). In particular Df is continuous (ContDiff.continuous_fderiv).

2. Unit field. Let w(x) := (InnerProductSpace.toDual ℝ ℝⁿ).symm (Df(x)) ∈ ℝⁿ, the Riesz representative (gradient) of Df(x). Then:
- ⟨w(x), h⟩ = Df(x)h for all h (InnerProductSpace.toDual_symm_apply);
- |w(x)| = ‖Df(x)‖, because toDual is a linear isometry equivalence;
- w is continuous;
- in particular Df(x)(w(x)) = ⟨w(x), w(x)⟩ = |w(x)|² (real_inner_self_eq_norm_sq).
Define s(x) := |w(x)|⁻¹ w(x) for x ∈ Q_δ, and s(x) := 0 for x ∉ Q_δ. With 0⁻¹ = 0, this also gives s(x) = 0 where w(x) = 0; in Lean, s = Q_δ.indicator (fun x => ‖w x‖⁻¹ • w x). Then:
 (a) s is Borel measurable: w is continuous and Q_δ is measurable (Measurable.indicator).
 (b) |s(x)| ≤ 1 for all x, since |w|⁻¹ |w| ∈ {0, 1}.
 (c) s(x) = 0 for x ∉ Q_δ.
 (d) s is integrable. It is the indicator of Q_δ of a measurable function bounded by 1, and vol(Q_δ) < ∞ (integrable_indicator_iff, Measure.integrableOn_of_bounded).
 (e) Df(x)(s(x)) = 1_{Q_δ}(x) ‖Df(x)‖ for all x. For x ∈ Q_δ, Df(x)(|w|⁻¹ w) = |w|⁻¹ |w|² = |w| = ‖Df(x)‖; both sides are 0 if w(x) = 0. For x ∉ Q_δ, both sides are 0.

3. Reflected kernel. ρ̌(z) := ρ(−z) satisfies:
- ρ̌ is C^∞ (ContDiff.comp contDiff_neg) and ρ̌ ≥ 0;
- ∫ρ̌ = ∫ρ = 1, since Lebesgue measure is invariant under z ↦ −z (integral_neg_eq_self);
- support ρ̌ ⊆ B_σ(0): if ρ̌(z) ≠ 0 then −z ∈ support ρ, so |z| = |−z| < σ.

4. Smoothed field. Let G := ρ̌ ⋆ s, i.e. G(y) = ∫ ρ(−t) s(y − t) dt. Apply smoothed_field with m, δ, σ, the kernel ρ̌ and the field s. Its hypotheses hold by 0(a), step 3 and 2(a)–(c). So G is C^∞, has compact support, tsupport G ⊆ Q₁, and |G(y)| ≤ 1 for all y.

5. Testing hyp(u, V). The field −G is admissible:
- it is C^∞ (ContDiff.neg) with compact support (HasCompactSupport.neg);
- tsupport(−G) = tsupport G ⊆ Q₁ (tsupport_neg);
- |−G(y)| = |G(y)| ≤ 1.
Hence ∫_{Q₁} u · div(−G) ≤ V. Now D(−G)(y) = −DG(y) (fderiv_neg) and the trace is linear (ContinuousLinearMap.toLinearMap_neg, map_neg), so div(−G) = −div G. Therefore (integral_neg)
   −∫_{Q₁} u(y) div G(y) dy ≤ V.   (5.1)

6. Adjoint identity. Apply mollify_adjoint with P = n, η = ρ (C¹ with compact support by 0(f)), the integrable function ū (by 0(e)) and the integrable field s (by 2(d)). The reflected kernel of ρ is ρ̌, ρ̌ ⋆ s = G, and ρ ⋆ ū = f, so
   ∫ Df(x)(s(x)) dx = −∫ ū(z) div G(z) dz.   (6.1)

7. Restriction to Q₁. ū(z) div G(z) = 1_{Q₁}(z) · (u(z) div G(z)), so ∫_{ℝⁿ} ū div G = ∫_{Q₁} u div G (integral_indicator with 0(b)).

8. Conclusion. Using integral_indicator (Q_δ is measurable), then 2(e), (6.1), step 7 and (5.1):
   ∫_{Q_δ} ‖Df(x)‖ dx = ∫_{ℝⁿ} 1_{Q_δ}(x) ‖Df(x)‖ dx = ∫_{ℝⁿ} Df(x)(s(x)) dx = −∫_{ℝⁿ} ū div G = −∫_{Q₁} u div G ≤ V. ∎
If δ ≥ 1/2, then Q_δ = ∅, s ≡ 0 and G ≡ 0, and the chain reads 0 = 0 ≤ V. No separate case is needed, and V ≥ 0 is never used.

Formalization note: with the two sibling declarations available, this chain has a complete Lean proof of about 120 lines. It uses only `import GMT.Ch07.Submission` and the lemmas named above, and its axioms are propext, Classical.choice and Quot.sound.

## Key steps

1. f = ρ⋆1_{Q₁}u is C^∞. Q_δ ⊆ Q₁ are measurable with finite measure, 1_{Q₁}u is integrable, and ρ has compact support.
2. s := 1_{Q_δ} w/|w| (w = Riesz representative of Df) is measurable, |s| ≤ 1, integrable, and Df(x)(s(x)) = 1_{Q_δ}(x)‖Df(x)‖.
3. ρ̌(z) = ρ(−z) satisfies the kernel hypotheses. By smoothed_field, G = ρ̌⋆s is C^∞, compactly supported in Q₁ and |G| ≤ 1, so hyp applied to −G gives −∫_{Q₁} u div G ≤ V.
4. mollify_adjoint with η = ρ gives ∫ Df(s) = −∫ 1_{Q₁}u div G = −∫_{Q₁} u div G.
5. ∫_{Q_δ}‖Df‖ = ∫ Df(s) = −∫_{Q₁} u div G ≤ V.

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
