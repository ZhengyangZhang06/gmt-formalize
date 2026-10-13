# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.simons_cone-a1`
- Child DAG node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.simons_regular_cone-a1.hypercone_plane-a1.simons_cone-a1.hardy_vanishing-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source. Simon Appendix B, proof of B.2 after (3) (chapter-B.txt lines 250–282: the extension of (3) under (4), the cut-offs γ_ε, the polar formula (5) and the choice (6)), as in steps 5–7 of the parent proof. Documented departures, inherited from the parent proof: (i) the finiteness statements obtained in print from the polar formula (5) are obtained from the dyadic estimates of the sibling cone_measure; (iii) the printed cut-off parameter ε is called κ. Here (3) for compactly supported test functions is the hypothesis (H3); the parent obtains it from the sibling simons_hardy. The exponent ε = 1/10 is the witness of SimonGMT AppendixB.exists_final_exponent.

Notation. μ := μHE[m], with ∫_M … dμ meaning ∫ x in M, … ∂μHE[m]. r(x) := |x|. T_x := tangentSpace M x; P_x := orthogonal projection onto span T_x; e_j the standard basis; δ_jg(x) := fderivWithin ℝ g M x (P_xe_j). |A|²(x) := Σ_j|Dν(x)(P_xe_j)|². Fix the open O ⊇ M on which ν is C^∞. If M = ∅ there is nothing to prove; assume M ≠ ∅.

1. (Cone facts.)
 (a) tM = M for t > 0 (apply the cone property with t and t⁻¹). M = closure(M) ∖ {0} is Borel, because 0 ∉ M and closure(M) ⊆ M ∪ {0}. For 0 < a ≤ b, M ∩ {a ≤ r ≤ b} = closure(M) ∩ {a ≤ r ≤ b} is closed and bounded, hence compact.
 (b) By normal_complement, T_x = A₀ ∩ ν(x)^⊥ is a linear subspace for x ∈ M (so span T_x = T_x), and P_x = P̃(x) := Π − ν(x)⊗ν(x), where Π is the projection onto A₀. Hence |A|² = Ã on M with Ã(y) := Σ_j|Dν(y)(P̃(y)e_j)|², which is continuous on O. So |A|² is continuous on M, and |A|² ≥ 0.
 (c) By cone_normal (with IsEmbeddedSubmanifold 1 m M): for x ∈ M and t > 0, x ∈ T_x, T_{tx} = T_x (so P_{tx} = P_x), and t·Dν(tx)v = Dν(x)v for v ∈ T_x.
 (d) Homogeneity: |A|²(tx) = t⁻²|A|²(x) for x ∈ M and t > 0. Indeed |A|²(tx) = Σ_j|Dν(tx)(P_xe_j)|² = Σ_j|t⁻¹Dν(x)(P_xe_j)|², since P_xe_j ∈ T_x.
 (e) Bound: Σ₁ := M ∩ {r = 1} is compact by (a). Let c_Σ := max_{Σ₁}|A|² if Σ₁ ≠ ∅ and c_Σ := 0 otherwise. For x ∈ M, x/r(x) ∈ Σ₁ by the cone property, so |A|²(x) = r(x)⁻²|A|²(x/r(x)) ≤ c_Σ·r(x)⁻² by (d).

2. (Radial test functions.) Let u : (0,∞) → ℝ be differentiable at ρ₀ = r(x), x ∈ M, and let φ(y) := u(r(y)) for y ≠ 0. Then Σ_j(δ_jφ(x))² = u'(r(x))². Indeed φ is differentiable at x with Dφ(x)v = u'(r(x))·(x/r(x))·v, because the norm is differentiable away from 0. By tangent_fderiv, δ_jφ(x) = Dφ(x)(P_xe_j) = u'(r(x))·(x/r(x))·P_xe_j = u'(r(x))·(P_x(x/r(x)))·e_j = u'(r(x))·(x/r(x))·e_j, since P_x is self-adjoint and P_xx = x (x ∈ T_x). Finally Σ_j((x/r(x))·e_j)² = |x/r(x)|² = 1.

3. (Measure facts.) By cone_measure: (i) μ(M ∩ {r = c}) = 0 for every c > 0; (ii) ∫⁻_{M∩{r<1}} r^α dμ < ∞ for α > −m; (iii) ∫⁻_{M∖{r<1}} r^β dμ < ∞ for β < −m.

4. (The profile.) ε := 1/10. Let p(ρ) := ρ^{1+ε} for 0 < ρ ≤ 1 and p(ρ) := ρ^{2−m/2−ε} for ρ ≥ 1. This is ρ^{1+ε}·max(1, ρ)^{1−m/2−2ε}, the printed ψ = r^{1+ε}r₁^{1−n/2−2ε}. p is continuous, with p(1) = 1, and C^∞ on (0, 1) and on (1, ∞). There p'(ρ) = (1 + ε)ρ^ε and p'(ρ) = (2 − m/2 − ε)ρ^{1−m/2−ε} respectively. Hence p(ρ)²/ρ² = ρ^{2ε} on (0, 1) and ρ^{2−m−2ε} on (1, ∞), and p'(ρ)² = (1 + ε)²ρ^{2ε} on (0, 1) and (m/2 − 2 + ε)²ρ^{2−m−2ε} on (1, ∞).

5. (Finiteness, replacing (5).) Put I₁ := ∫_{M∩{r<1}} |A|²r^{2ε} dμ and I₂ := ∫_{M∩{r>1}} |A|²r^{2−m−2ε} dμ. The integrands are nonnegative and continuous on M, hence measurable. By 1(e), |A|²r^{2ε} ≤ c_Σr^{2ε−2}, and 2ε − 2 > −m because m ≥ 2 and ε > 0; so 3(ii) gives I₁ < ∞. Likewise |A|²r^{2−m−2ε} ≤ c_Σr^{−m−2ε}, and −m − 2ε < −m; so 3(iii) gives I₂ < ∞ (note {r > 1} ⊆ {r ≥ 1}). Since M ∩ {r = 1} is null (3(i)):
 J := ∫_M p(r)²|A|²/r² dμ = I₁ + I₂ < ∞,   K := ∫_M |A|²p'(r)² dμ = (1 + ε)²I₁ + (m/2 − 2 + ε)²I₂ < ∞.
 Here p'(r) is defined off the null set {r = 1}. Both integrands are integrable. This is the printed (4) for ψ = p(r).

6. (Cut-offs.) For 0 < κ < 1 let g_κ : [0, ∞) → [0, 1] be continuous and piecewise linear: 0 on [0, κ/2]; (2/κ)(ρ − κ/2) on [κ/2, κ]; 1 on [κ, κ⁻¹]; 2 − κρ on [κ⁻¹, 2κ⁻¹]; 0 on [2κ⁻¹, ∞). The breakpoints are ordered because κ < 1. Off the breakpoints, |g_κ'(ρ)| ≤ 3ρ⁻¹·1_{E_κ}(ρ) with E_κ := (κ/2, κ) ∪ (κ⁻¹, 2κ⁻¹). On (κ/2, κ), |g_κ'| = 2/κ < 2/ρ ≤ 3/ρ; on (κ⁻¹, 2κ⁻¹), |g_κ'| = κ < 2/ρ ≤ 3/ρ (the constant 3 is the printed one; 2 would do). Put u_κ := p·g_κ on (0, ∞) and φ_κ(y) := u_κ(r(y)) for y ≠ 0, φ_κ(0) := 0.
 (a) φ_κ is Lipschitz on ℝ^P, hence locally Lipschitz on M. u_κ vanishes on (0, κ/2] and on [2κ⁻¹, ∞). On [κ/2, 2κ⁻¹] it is continuous and piecewise C¹ with finitely many pieces and bounded derivative, so u_κ is Lipschitz on (0, ∞), and φ_κ = u_κ∘r with r 1-Lipschitz.
 (b) φ_κ vanishes on M outside C_κ := M ∩ {κ/2 ≤ r ≤ 2κ⁻¹}, a compact subset of M by 1(a).
 (c) By the hypothesis (H3) applied to φ_κ: 2∫_M φ_κ²|A|²/r² dμ ≤ ∫_M |A|²·Σ_j(δ_jφ_κ)² dμ.
 (d) Let Z_κ := M ∩ {r ∈ {κ/2, κ, 1, κ⁻¹, 2κ⁻¹}}, which is μ-null by 3(i). For x ∈ M ∖ Z_κ, u_κ is C¹ near r(x). By step 2, Σ_j(δ_jφ_κ(x))² = u_κ'(r)² = (p'g_κ + pg_κ')²(r). Fix η > 0. Using (a + b)² ≤ (1 + η)a² + (1 + η⁻¹)b², 0 ≤ g_κ ≤ 1 and the bound on g_κ':
 Σ_j(δ_jφ_κ(x))² ≤ (1 + η)p'(r)² + 9(1 + η⁻¹)·1_{E_κ}(r)·p(r)²/r².
 (e) Multiply by |A|² ≥ 0 and integrate. By (d), off the null set Z_κ, |A|²·Σ_j(δ_jφ_κ)² equals |A|²·u_κ'(r)², a bounded Borel function supported in the compact set C_κ. So it is integrable, and so is the right side (step 5). Then
 2∫_M g_κ(r)²p(r)²|A|²/r² dμ ≤ (1 + η)K + 9(1 + η⁻¹)∫_M 1_{E_κ}(r)p(r)²|A|²/r² dμ,
 because φ_κ² = g_κ(r)²p(r)².

7. (κ → 0.) Let κ_n := 1/(n + 2). For x ∈ M, 0 < r(x) < ∞. So for n large, κ_n < r(x) < κ_n⁻¹, giving g_{κ_n}(r(x)) = 1 and 1_{E_{κ_n}}(r(x)) = 0. Both integrands in 6(e) are dominated by the integrable function p(r)²|A|²/r² (step 5). By dominated convergence (tendsto_integral_of_dominated_convergence) the left side tends to 2J and the last integral tends to 0. Hence 2J ≤ (1 + η)K for every η > 0, and letting η → 0, 2J ≤ K. This is the printed (6).

8. (Choice of ε.) Step 7 reads 2(I₁ + I₂) ≤ (1 + ε)²I₁ + (m/2 − 2 + ε)²I₂, i.e.
 (2 − (1 + ε)²)I₁ + (2 − (m/2 − 2 + ε)²)I₂ ≤ 0.
 With ε = 1/10: (1 + ε)² = 1.21 < 2. For m ∈ {2, …, 6}, m/2 − 2 + ε ∈ {−0.9, −0.4, 0.1, 0.6, 1.1}, so (m/2 − 2 + ε)² ≤ 1.21 < 2. Both coefficients are positive and I₁, I₂ ∈ [0, ∞), so I₁ = I₂ = 0.

9. (|A|² = 0 a.e.) I₁ = 0 and r^{2ε} > 0 give |A|² = 0 μ-a.e. on M ∩ {r < 1}; similarly I₂ = 0 gives it on M ∩ {r > 1}. M ∩ {r = 1} is null (3(i)). So |A|² = 0 μ-a.e. on M.

10. (|A|² ≡ 0.) Suppose |A|²(x₀) > 0 for some x₀ ∈ M. By continuity on M (1(b)) there is δ > 0 with |A|² > 0 on M ∩ ball(x₀, δ). By the density hypothesis, μ(M ∩ ball(x₀, s))/(ω_m·s^m) → 1 as s ↓ 0, where ω_m = unitBallVolume m ∈ (0, ∞). So for some s ∈ (0, δ) the ratio exceeds ½, and μ(M ∩ ball(x₀, s)) > 0. But |A|² > 0 on this set and |A|² = 0 μ-a.e. on M (step 9), a contradiction. Hence |A|²(x) = 0 for every x ∈ M.

11. (Conclusion.) Let x ∈ M and v ∈ T_x. |A|²(x) = Σ_j|Dν(x)(P_xe_j)|² = 0 gives Dν(x)(P_xe_j) = 0 for every j. Since T_x is a subspace (1(b)), v = P_xv = Σ_j v_jP_xe_j. Hence fderiv ℝ ν x v = Σ_j v_j·Dν(x)(P_xe_j) = 0. ∎

## Key steps

1. Cone facts: compact annular slices, |A|² continuous on M, |A|²(tx) = t⁻²|A|²(x), hence |A|² ≤ c_Σ|x|⁻² on M.
2. Radial test functions u(|x|): Σ_j(δ_ju(|x|))² = u'(|x|)² since x ∈ T_x.
3. ψ = r^{1+ε}max(1,r)^{1−m/2−2ε}, ε = 1/10: I₁, I₂ < ∞ by cone_measure (dyadic estimates replace the polar formula).
4. Apply (H3) to ψ·g_κ(|x|), bound |∇^M|² with (1+η), (1+η⁻¹), spheres are null; dominated convergence as κ → 0, then η → 0.
5. 2(I₁+I₂) ≤ (1+ε)²I₁ + (m/2−2+ε)²I₂ with both coefficients < 2 ⇒ I₁ = I₂ = 0 ⇒ |A|² = 0 a.e.; continuity and density one ⇒ |A|² ≡ 0 ⇒ Dν(x) = 0 on T_x.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD`
- `rg -n 'Simons|Codazzi|Laplace|second fundamental' project/GMT`
- `rg -n 'def tangentSpace|def IsEmbeddedSubmanifold' project/GMT/Ch07/Contract.lean`
- `rg -n 'theorem HasFDerivWithinAt.unique_on|theorem DifferentiableWithinAt.hasFDerivWithinAt|mem_tangentConeAt_of_seq|irreducible_def tangentConeAt|irreducible_def fderivWithin' mathlib/Mathlib/Analysis/Calculus`
- `rg -n 'hausdorffMeasure_smul₀|hausdorffMeasure_image_le|EuclideanSpace.euclideanHausdorffMeasure_eq_volume' mathlib/Mathlib`
- `rg -n '^theorem|^lemma' mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `rg -n 'isSymmSndFDerivAt|exists_orthonormalBasis_extension|ContDiffOn.fderiv_of_isOpen|exists_contDiff_support_eq_eq_one_iff|eq_starProjection_of_mem_of_inner_eq_zero|eq_of_le_of_finrank_eq|IsLocalMin.hasDerivAt_eq_zero|tendsto_integral_of_dominated_convergence|ContinuousOn.aestronglyMeasurable|ae_restrict_iff' mathlib/Mathlib`
- `rg -n 'def localInverse|theorem eventually_left_inverse|theorem to_localInverse' mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem`
- `rg -n 'theorem exists_smooth_tsupport_subset|theorem HasStrictFDerivAt.to_localInverse|theorem LocallyLipschitzOn' mathlib/Mathlib (no match under these exact names)`
- `grep -n 'theorem|def' simongmt/Poincare/SimonGMT/AppendixB/{SimonsInequalities,ConeDefect,LagrangeIdentity}.lean; lean Avail.lean: #check Poincare.SimonGMT.AppendixB.cone_simonsDefect_lower_bound after import GMT.Ch07.Submission`
- `python3 scans of dag.json (nodes under hypercone_plane-a1, statuses and frozen types of chart_tangentSpace_eq_range_fderiv, dimred_rpd_submanifold_density_one, codim1_hcp_lipschitz_smooth_approx, codim1_hcp_smooth_charts); grep -c codim1_hcp_sc dag.json; git log --all -S codim1_hcp_sc -- GMT`
- `lean -DautoImplicit=false /tmp/simons-cone-split/check/{Parent,TypesAll,Assembly,Inst}.lean with LEAN_PATH = .lake/build/lib/lean plus every package's .lake/build/lib/lean`
- `python3 verifier/lean_contract.py validate_lean_statement on all 12 child types`
- `/tmp/simons-cone-venv/env/bin/python -I /tmp/simons-cone-split/scripts/jets.py {clifford,more} and generic2.py {ell,gen3,cubic}`
- `book/chapter-B.txt lines 1–282 (B.1–B.11 and proof of B.2)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/TangentCone/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixB/ConeDefect.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixB/SimonsInequalities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/AppendixB/LagrangeIdentity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-a3c4818ec8/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-sim-b5d5990773/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-B.txt`
- `/tmp/simons-cone-split/check/TypesAll.lean`
- `/tmp/simons-cone-split/check/Assembly.lean`
- `/tmp/simons-cone-split/check/Inst.lean`
- `/tmp/simons-cone-split/scripts/jets.py`

Pins match. The snapshot manifest records project b4d606db and Mathlib 25730c7c; these equal the workspace HEAD and .lake/packages/mathlib (simongmt is at 2b366308). The snapshot's project/GMT/Ch07/Contract.lean, the workspace Contract.lean and Submission.lean are byte-identical (sha256 e4148e7f9503aa28…).

Project: there is no Simons, Codazzi or Laplace–Beltrami development. rg finds only the Ch02 B_y doc-comment, the Ch07 'Simons cone' remark and README pointers to the AppendixB numerics. tangentSpace (Contract.lean:228) and IsEmbeddedSubmanifold (:221) are the definitions used.

Mathlib snapshot: it contains every library fact the child proofs cite.
- HasFDerivWithinAt.unique_on (FDeriv/Basic.lean:159) and DifferentiableWithinAt.hasFDerivWithinAt (:391); the fderivWithin definition (FDeriv/Defs.lean:151); mem_tangentConeAt_of_seq (TangentCone/Defs.lean:96).
- Measure.hausdorffMeasure_smul₀ (Hausdorff.lean:753); LipschitzOnWith.hausdorffMeasure_image_le (:733); LipschitzOnWith.ae_differentiableWithinAt_of_mem (Rademacher.lean:361); EuclideanSpace.euclideanHausdorffMeasure_eq_volume (Geometry/Euclidean/Volume/Measure.lean:187).
- ContDiffAt.isSymmSndFDerivAt (FDeriv/Symmetric.lean:533); Orthonormal.exists_orthonormalBasis_extension (PiL2.lean:1031); ContDiffOn.fderiv_of_isOpen (ContDiff/Defs.lean:907); exists_contDiff_support_eq_eq_one_iff (PartitionOfUnity.lean:789); HasStrictFDerivAt.localInverse, eventually_left_inverse and to_localInverse (InverseFunctionTheorem/FDeriv.lean:149–186).
- Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Projection/Basic.lean:180); Submodule.eq_of_le_of_finrank_eq (FiniteDimensional/Basic.lean:257); IsLocalMin.hasDerivAt_eq_zero (LocalExtr/Basic.lean:237); tendsto_integral_of_dominated_convergence (DominatedConvergence.lean:57); ae_restrict_iff' (Restrict.lean:629).
- No match for theorems named exists_smooth_tsupport_subset or HasStrictFDerivAt.to_localInverse. The proofs use exists_contDiff_support_eq_eq_one_iff and the namespaced inverse-function lemmas instead.

SimonGMT: AppendixB supplies the B.10–B.11 algebra (ConeDefect.lean:136–228, LagrangeIdentity.lean:122) and ε = 1/10 (SimonsInequalities.lean:88). However, #check of cone_simonsDefect_lower_bound after import GMT.Ch07.Submission gives Unknown identifier. Child statements therefore avoid it, and cone_defect's proof notes the extra import and includes the printed algebra.

DAG: chart_tangentSpace_eq_range_fderiv is accepted (candidate d626082a69a0) and is reused with an identical type. lipschitz_approx and smooth_charts are unaccepted children of this node's parent, so they cannot be reused here. lipschitz_approx's exact conclusion is passed as hypothesis (HL), and density one as a hypothesis; the parent discharges both from its own resolved dependencies. The codim1_hcp_sc_ names are free in dag.json, in the git history and in all reference trees.

Lean: all 12 types elaborate (TypesAll, exit 0), and the parent's frozen type is kernel-checked from them (Assembly, exit 0).
