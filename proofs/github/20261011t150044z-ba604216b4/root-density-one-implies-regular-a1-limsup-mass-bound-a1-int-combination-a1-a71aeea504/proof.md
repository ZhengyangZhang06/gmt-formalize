# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1`
- Child DAG node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.int_combination-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 6, Remark 3.2(1) (chapter-06.txt lines 755–757), which is stated there without proof. The argument uses the orientation conventions of Ch. 6, 3.1 and the locality of approximate tangent spaces (sibling tangent_locality; Ch. 3, Remark 1.5(2)).
Notation: R = (M, θ, ξ) is an IMRep in U, μ_R = θHⁿ⌞M, and R represents T means T(ω) = ∫_M θ ξ(ω) dHⁿ. An n-vector ζ orients an n-dimensional subspace Q if ζ(α) = ±α(τ₁,…,τₙ) for all n-covectors α, for some orthonormal basis τ of Q (IsUnitOrientationOf). For an increasing multi-index I = (i₁ < ⋯ < iₙ) let dx^I be the n-covector (v₁,…,vₙ) ↦ det[(v_j)_{i_k}]; for n = 0, dx^∅ = 1.
1. Linear algebra.
 (a) If ζ orients Q via the orthonormal τ, then |ζ(α)| = |α(τ)| ≤ ‖α‖ (operator norm) for every n-covector α. Also Σ_I ζ(dx^I)² = Σ_I det[(τ_j)_{i_k}]² = det(τ_i·τ_j) = 1 (Cauchy–Binet).
 (b) If ζ and ζ' both orient Q (orthonormal bases τ, τ'), then τ'_j = Σ_i O_{ij}τ_i with O orthogonal, so α(τ') = det(O)α(τ) for every alternating α. Hence ζ' = ±ζ, and Σ_I ζ(dx^I)ζ'(dx^I) = ±1 with the same sign.
2. Setup.
 (a) Since θᵢ ≥ 1 on Mᵢ, Hⁿ(Mᵢ ∩ K) ≤ ∫_{Mᵢ∩K}θᵢ dHⁿ < ∞ for compact K ⊆ U. Hence M' := M₁ ∪ M₂ is a Borel subset of U with Hⁿ(M' ∩ K) < ∞.
 (b) ξᵢ is a.e.-strongly measurable for Hⁿ⌞Mᵢ. Choose Borel maps ξ̃ᵢ : ℝ^P → Λ_n with ξ̃ᵢ = ξᵢ Hⁿ-a.e. on Mᵢ.
3. Overlap.
 (a) For Hⁿ-a.e. x ∈ Mᵢ, T_xMᵢ exists and ξᵢ(x) orients it (IMRep).
 (b) Apply tangent_locality to (A, B) = (M₁ ∩ M₂, M₁) and to (M₁ ∩ M₂, M₂). For Hⁿ-a.e. x ∈ M₁ ∩ M₂ this gives T_xM₁ = T_x(M₁ ∩ M₂) = T_xM₂.
 (c) Let σ : ℝ^P → {−1, 1} be the Borel function σ(x) := 1 if Σ_I ξ̃₁(x)(dx^I) ξ̃₂(x)(dx^I) ≥ 0 and σ(x) := −1 otherwise. By (a), (b) and 1(b), ξ̃₂(x) = σ(x) ξ̃₁(x) for Hⁿ-a.e. x ∈ M₁ ∩ M₂.
4. Definition of R.
 (a) Define the Borel function m : ℝ^P → ℤ by m := p₁θ₁ + σp₂θ₂ on M₁ ∩ M₂, m := p₁θ₁ on M₁ ∖ M₂, m := p₂θ₂ on M₂ ∖ M₁, and m := 0 off M'. Let sgn(m) := 1 if m ≥ 0 and −1 if m < 0.
 (b) Let M := {x ∈ M' : m(x) ≠ 0} and θ := |m| (ℕ-valued).
 (c) Let ξ := sgn(m)ξ̃₁ on M₁, ξ := sgn(m)ξ̃₂ on M₂ ∖ M₁, and ξ := 0 elsewhere. Set R := (M, θ, ξ).
5. Pointwise identities. For Hⁿ-a.e. x ∈ M' and every n-covector α:
 (†) p₁θ₁(x)1_{M₁}(x)ξ₁(x)(α) + p₂θ₂(x)1_{M₂}(x)ξ₂(x)(α) = θ(x)ξ(x)(α).
 - On M₁ ∖ M₂ both sides equal p₁θ₁ξ̃₁(α) = |m| sgn(m) ξ̃₁(α).
 - On M₂ ∖ M₁ the same holds with index 2.
 - On M₁ ∩ M₂ (a.e., by 3(c)) the left side is (p₁θ₁ + p₂θ₂σ)ξ̃₁(α) = mξ̃₁(α) = θξ(α).
 Moreover 0 ≤ θ ≤ |p₁|θ₁1_{M₁} + |p₂|θ₂1_{M₂} everywhere, by the triangle inequality.
6. R is an IMRep in U.
 (a) M is Borel and M ⊆ M' ⊆ U. M is countably n-rectifiable, being a subset of a union of two countably n-rectifiable sets (finitely many exceptional null sets and countably many Lipschitz images combine; SimonGMT CountablyRectifiable.mono).
 (b) θ is measurable and θ ≥ 1 on M.
 (c) For compact K ⊆ U, ∫_{M∩K}θ dHⁿ ≤ |p₁|∫_{M₁∩K}θ₁ + |p₂|∫_{M₂∩K}θ₂ < ∞.
 (d) ξ is Borel, hence a.e.-strongly measurable.
 (e) Orientation on M ∩ M₁. Apply tangent_locality to (M ∩ M₁, M₁) and to (M ∩ M₁, M); both are legitimate since Hⁿ(M ∩ K) < ∞. For Hⁿ-a.e. x ∈ M ∩ M₁ this gives T_xM = T_x(M ∩ M₁) = T_xM₁. The latter is oriented by ξ₁(x) = ξ̃₁(x), hence by ξ(x) = ±ξ̃₁(x).
 (f) Orientation on M ∩ (M₂ ∖ M₁): the same argument with M₂ in place of M₁.
 So for Hⁿ⌞M-a.e. x, T_xM exists and ξ(x) orients it.
7. R represents S. Let ω ∈ 𝒟ⁿ(U) with spt ω ⊆ K, K compact ⊆ U. By 1(a), |θᵢξᵢ(ω)| ≤ θᵢ1_K sup‖ω‖ a.e., which is integrable. Using (†),
 S(ω) = p₁T₁(ω) + p₂T₂(ω) = ∫_{M'} [p₁θ₁1_{M₁}ξ₁(ω) + p₂θ₂1_{M₂}ξ₂(ω)] dHⁿ = ∫_{M'} θξ(ω) dHⁿ = ∫_M θξ(ω) dHⁿ.
 The last equality holds because θ = 0 on M' ∖ M.
8. Measure bound. For every Borel set E, step 5 gives μ_R(E) = ∫_{M∩E}θ dHⁿ ≤ |p₁|∫_{M₁∩E}θ₁ dHⁿ + |p₂|∫_{M₂∩E}θ₂ dHⁿ = |p₁|μ_{R₁}(E) + |p₂|μ_{R₂}(E). Hence μ_R ≤ |p₁|μ_{R₁} + |p₂|μ_{R₂} as measures. ∎

## Key steps

1. On M₁ ∩ M₂ the approximate tangent planes coincide a.e. (tangent_locality), so ξ̃₂ = σξ̃₁ with a Borel sign σ.
2. Define m := p₁θ₁1_{M₁} + σp₂θ₂1_{M₂} (integer valued), carrier M := {m ≠ 0}, θ := |m|, ξ := sgn(m)·(ξ̃₁ or ξ̃₂).
3. Tangent locality again shows ξ orients T_xM a.e.; the pointwise identity p₁θ₁ξ₁ + p₂θ₂ξ₂ = θξ gives S = τ(M, θ, ξ).
4. θ ≤ |p₁|θ₁ + |p₂|θ₂ pointwise gives μ_R ≤ |p₁|μ_{R₁} + |p₂|μ_{R₂}.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (both identical)`
- `rg -c sorry local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean (1, the final main_theorem)`
- `rg -l -i 'slice|slicing|flat metric|flat norm|deformation theorem|nearest.point|tubular' simongmt/Poincare/SimonGMT local-references/123e8435b4a2469b/project -t lean`
- `rg -n 'def .*[Pp]ushforward' simongmt/Poincare/SimonGMT -t lean`
- `rg -n -i 'theorem .*area.*rectifiable|rectifiable.*area_formula|areaFormula.*Rectifiable' simongmt/Poincare/SimonGMT -t lean (no match)`
- `grep -n '^theorem|^def' simongmt Chapter02/AreaNoninjective.lean, Chapter03/{SubmanifoldCover,DisjointCover,Rectifiable,Differential}.lean, Chapter06/{Currents,Mass,CurrentLocalEquality,Forms}.lean`
- `grep -n 'measure_compl_support|hausdorffMeasure_image_le|norm_image_sub_le_of_norm_fderiv_le|toOpenPartialHomeomorph|exists_isCompact_diff_lt' in snapshot mathlib Support.lean, Hausdorff.lean, MeanValue.lean, InverseFunctionTheorem/ContDiff.lean, Regular.lean`
- `grep -rln 'def compContinuousLinearMap' snapshot mathlib Topology/Algebra/Module/Alternating`
- `dag.json lean_name scan for the eight proposed dor_lmb_* names (164 nodes at 2026-10-12T01:39Z; no collision); git grep dor_lmb over all branches (no match)`
- `python3 -I: verifier/lean_contract.py validate_lean_statement and verifier/gmt-compare.py contract_scope on all eight lean_statement strings`
- `lake env lean /tmp/lmb-decomp-v2/Types.lean (eight child types in the exact comparator scope, each also checked as `example : Prop`)`
- `lake env lean /tmp/lmb-decomp-v2/Assembly.lean (#print axioms Submission.dor_minimizing_limsup_mass_bound)`
- `lake env lean /tmp/lmb-decomp-v2/Inst.lean (implicit volume on ℝ, Measure.le_iff', ENNReal smul of measures)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/MeanValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/AreaNoninjective.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinear.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/DisjointCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Product.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter08/DeformationIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1/decomposition-audit-v1.json`
- `/tmp/lmb-decomp-v2/v2_subproblems.json`
- `/tmp/lmb-decomp-v2/Types.lean`
- `/tmp/lmb-decomp-v2/Assembly.lean`
- `/tmp/lmb-decomp-v2/Inst.lean`

Snapshot: project b4d606d, mathlib 25730c7c; simongmt is pinned at 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean. Its only sorry is main_theorem.

Reusable facts found:
- SimonGMT Chapter03/Rectifiable.lean: HasApproximateTangentSpaceAt (Simon 1.4, unweighted), .unique, CountablyRectifiable and CountablyRectifiable.mono.
- Chapter03/DisjointCover.lean: simon_remark_1_3 (disjoint Borel pieces).
- Chapter03/SubmanifoldCover.lean: countablyRectifiable_of_submanifold_cover, measurableSet_of_isSimonSubmanifold, countablyRectifiable_image_contDiffOn_open. Its header says the converse direction of Lemma 1.2 "remains a separate theorem".
- Chapter02/AreaNoninjective.lean: weighted_area_formula_lipschitz_fiberSum, a non-injective weighted Lipschitz area formula. It is for maps on a Euclidean domain, not on rectifiable subsets of ℝ^P.
- Chapter06: massOn and massAdmissibleOn (Mass.lean); support as U minus the zero region (CurrentLocalEquality.lean); GeometricCurrentOn with sequential continuity, and boundary (Currents.lean).
- Mathlib: measure_compl_support, LipschitzOnWith.hausdorffMeasure_image_le, Convex.norm_image_sub_le_of_norm_fderiv_le, ContDiffAt.toOpenPartialHomeomorph, MeasurableSet.exists_isCompact_diff_lt, ContinuousAlternatingMap.compContinuousLinearMap, μHE[d].

Not available, so cited from Simon in the child proofs:
- current slicing (6.4) and flat convergence (6.7.2): the keyword hits are only linear co-area slices, product point slices and varifold deformation slices;
- the Deformation Theorem (6.5.3) and completeness (6.3.13);
- C¹ or Lipschitz push-forward of currents: only affinePushforward and varifold push-forwards exist;
- the rectifiable-set area formula (Ch. 3, 2.6), the only-if direction of Lemma 1.2, and a nonlinear tubular-neighbourhood retraction.

Lean checks:
- All eight child types elaborate as Prop in the exact comparator scope and pass validate_lean_statement.
- The conditional assembly of the exact frozen parent type compiles. It depends only on propext, Classical.choice, Quot.sound and the stubs' sorryAx.
- No proposed name collides.
