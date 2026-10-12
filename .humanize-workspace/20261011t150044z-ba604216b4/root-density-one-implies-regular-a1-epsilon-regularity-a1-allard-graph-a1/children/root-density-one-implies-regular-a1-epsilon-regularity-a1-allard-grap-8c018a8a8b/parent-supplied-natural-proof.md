# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.graph_tangent-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Part 1.6 (Simon Ch. 3, 1.5(2) and the proof of 1.6; Ch. 1, 3.6 and Remark 3.7(2); Ch. 2, 3.5). Conventions: E := ℝ^{n+k}; B_λ(x) closed ball, Bⁿ_λ(v) closed ball of ℝⁿ; M := R.carrier, θ := R.mult, Hⁿ := μHE[n] (equal to Lebesgue measure Lⁿ on ℝⁿ and on every n-plane), ω_n := unitBallVolume n. For x, λ > 0, η_{x,λ}(y) := λ^{−1}(y − x) (library blowUpMap), so Hⁿ(η_{x,λ}(A)) = λ^{−n}Hⁿ(A). "M has approximate tangent plane P at x" means HasApproximateTangentSpaceAt n M x P: dim P = n and ∫_{η_{x,λ}(M)}ψ dHⁿ → ∫_P ψ dHⁿ as λ ↓ 0 for every continuous compactly supported ψ : E → ℝ.

0. Setup. Let Φ(v) := a + ιv + ι'(f v) (v ∈ ℝⁿ) and F := Φ(ℝⁿ). Since ι, ι' are linear isometries with orthogonal ranges, |Φ(v₁) − Φ(v₂)|² = |v₁ − v₂|² + |f(v₁) − f(v₂)|²; hence Φ is injective, Lipschitz with constant (1 + L²)^{1/2}, and |v₁ − v₂| ≤ |Φ(v₁) − Φ(v₂)|. For each x ∈ F there is exactly one v with x = Φ(v). For v where f is differentiable let P_v := LinearMap.range(ι + ι'∘Df(v)) = {ιw + ι'Df(v)w : w ∈ ℝⁿ}, an n-plane (w ↦ ιw + ι'Df(v)w is injective), and J(v) := (det(I + Df(v)ᵀDf(v)))^{1/2} ∈ [1, (1 + L²)^{n/2}], the area Jacobian of Φ at v; A ↦ (det(I + AᵀA))^{1/2} is smooth, hence Lipschitz on {‖A‖ ≤ L}.
1. Good parameters. By Rademacher's theorem (Mathlib LipschitzWith.ae_differentiableAt) f is differentiable at Lⁿ-a.e. v; Df (defined a.e.) is bounded and measurable, so by Lebesgue's differentiation theorem Lⁿ-a.e. v is a Lebesgue point of Df: λ^{−n}∫_{Bⁿ_λ(v)}|Df(v') − Df(v)|dv' → 0. Let N be the Lⁿ-null set of v at which one of these fails. Since Φ is Lipschitz, Hⁿ(Φ(N)) ≤ (1 + L²)^{n/2}Hⁿ(N) = 0 (Mathlib LipschitzWith/LipschitzOnWith.hausdorffMeasure_image_le).
2. F has approximate tangent plane P_v at x = Φ(v) for v ∉ N. Let ψ be continuous with spt ψ ⊆ B_{R'}(0), and λ > 0. Since F ∩ K ⊆ Φ(Bⁿ_m(0)) for every compact K and large m, Hⁿ(F ∩ K) < ∞, so ψ is integrable for Hⁿ⌞η_{x,λ}(F) and the Bochner integrals in the library definition of HasApproximateTangentSpaceAt are genuine integrals. Write ψ = ψ⁺ − ψ⁻ with ψ^± := max{±ψ, 0} continuous, nonnegative and supported in B_{R'}(0); the identities below are first obtained for ψ^± (the library area formulas are lower-integral statements with nonnegative weights) and then subtracted, all terms being finite. By the area formula for the injective Lipschitz map Φ (Simon Ch. 2, 3.5–3.7; library injective_area_formula_lipschitz / weighted_area_formula_lipschitz_injOn) and the scaling of Hⁿ, ∫_{η_{x,λ}(F)}ψ dHⁿ = λ^{−n}∫_F ψ(η_{x,λ}(y))dHⁿ(y) = λ^{−n}∫_{ℝⁿ}ψ((Φ(v') − x)/λ)J(v')dv' = ∫_{ℝⁿ}ψ(ιw + ι'f_λ(w))J(v + λw)dw, where f_λ(w) := (f(v + λw) − f(v))/λ (substitution v' = v + λw). As |ιw + ι'f_λ(w)| ≥ |w|, the integrand vanishes for |w| > R', and it is bounded by sup|ψ|(1 + L²)^{n/2}. As λ ↓ 0: f_λ → Df(v) uniformly on Bⁿ_{R'}(0) (differentiability at v), so ψ(ιw + ι'f_λ(w)) → ψ(ιw + ι'Df(v)w) uniformly there (ψ is uniformly continuous); and ∫_{Bⁿ_{R'}(0)}|J(v + λw) − J(v)|dw = λ^{−n}∫_{Bⁿ_{λR'}(v)}|J − J(v)| ≤ Lip·λ^{−n}∫_{Bⁿ_{λR'}(v)}|Df − Df(v)| → 0 (Lebesgue point). Hence ∫_{η_{x,λ}(F)}ψ dHⁿ → ∫_{ℝⁿ}ψ(ιw + ι'Df(v)w)J(v)dw = ∫_{P_v}ψ dHⁿ, the last equality by the area formula for the injective linear map w ↦ ιw + ι'Df(v)w, whose Jacobian is J(v). Thus HasApproximateTangentSpaceAt n F x P_v.
3. Vanishing densities. Let A₁ := (M ∖ F) ∩ W and A₂ := F ∖ M; both are Borel (M is Borel, F = ∪_m Φ(Bⁿ_m(0)) is σ-compact). Write W = ∪_j V_j with V_j := {y ∈ W : |y| < j, dist(y, E ∖ W) > 1/j} (V_j := {|y| < j} if W = E); each V_j is open with compact closure in W. Each Borel set A_i ∩ V_j has finite Hⁿ-measure: for compact K ⊆ W, Hⁿ(M ∩ K) ≤ ∫_{M∩K}θ dHⁿ < ∞ (θ ≥ 1 on M, IMRep.locallyIntegrable_mult, K ⊆ U), and F ∩ K ⊆ Φ(Bⁿ_m(0)) for m ≥ sup_K|y − a|, whose Hⁿ-measure is ≤ (1+L²)^{n/2}ω_nmⁿ < ∞. By the Upper Density Theorem (Simon Ch. 1, 3.6; library simon_theorem_3_6, applied to the Borel regular outer measure Hⁿ and the Hⁿ-measurable set A_i ∩ V_j of finite measure), limsup_{λ↓0}Hⁿ(A_i ∩ V_j ∩ B_λ(x))/λⁿ = 0 for Hⁿ-a.e. x ∉ A_i ∩ V_j (library glue: apply simon_theorem_3_6 to the Borel regular outer measure of Hⁿ⌞(A_i ∩ V_j) (measure_toOuterMeasure_isBorelRegular) and transfer the Simon-normalized null set to μHE[n] by simonHausdorffMeasureReal_nat_eq_smul_euclideanHausdorffMeasure; both have the same null sets). If x ∈ V_j then B_λ(x) ⊆ V_j for small λ, so limsup_{λ↓0}Hⁿ(A_i ∩ B_λ(x))/λⁿ = 0. Taking the (countable) union over j of the exceptional sets: the density of Hⁿ⌞A_i vanishes at Hⁿ-a.e. x ∈ W ∖ A_i (i = 1, 2), in particular at Hⁿ-a.e. x ∈ M ∩ F ∩ W, which is disjoint from A₁ ∪ A₂.
4. Transfer to M. Let x ∈ M ∩ F ∩ W, x = Φ(v), with v ∉ N and with both densities of 3 equal to 0 at x. For ψ as in 2 with spt ψ ⊆ B_{R'}(0) and λ small enough that B_{λR'}(x) ⊆ W (then Hⁿ(M ∩ B_{λR'}(x)) < ∞, as θ ≥ 1 on M and IMRep.locallyIntegrable_mult applies to the compact set B_{λR'}(x) ⊆ W ⊆ U, so both integrals below are genuine Bochner integrals): |∫_{η_{x,λ}(M)}ψ dHⁿ − ∫_{η_{x,λ}(F)}ψ dHⁿ| ≤ sup|ψ|·λ^{−n}Hⁿ((M △ F) ∩ B_{λR'}(x)) ≤ sup|ψ|·λ^{−n}(Hⁿ(A₁ ∩ B_{λR'}(x)) + Hⁿ(A₂ ∩ B_{λR'}(x))) → 0. With 2, ∫_{η_{x,λ}(M)}ψ dHⁿ → ∫_{P_v}ψ dHⁿ, i.e. HasApproximateTangentSpaceAt n M x P_v. Therefore the existential condition in the definition of approxTangentPlane holds at x and, by uniqueness (HasApproximateTangentSpaceAt.unique), approxTangentPlane n M x = P_v = LinearMap.range(ι + ι'∘Df(v)); moreover f is differentiable at v since v ∉ N.
5. Conclusion. Let Z := Φ(N) ∪ Z₁ ∪ Z₂, where Z_i is the Hⁿ-null exceptional set of 3 for A_i; Hⁿ(Z) = 0. For x ∈ (M ∩ W) ∖ Z and any v with x = a + ιv + ι'(f v): x ∈ M ∩ F ∩ W, v is the unique parameter of x, v ∉ N (as x ∉ Φ(N)), and both densities vanish at x; by 4, f is differentiable at v and approxTangentPlane n M x = LinearMap.range(ι.toLinearMap + ι'.toLinearMap ∘ Df(v)). For x ∉ F the implication is vacuous. Since Z is Hⁿ-null, the assertion holds for μHE[n].restrict (M ∩ W)-a.e. x. ∎

## Key steps

1. Rademacher and Lebesgue differentiation: off an Lⁿ-null set N, f is differentiable with Lebesgue points of Df, and Hⁿ(Φ(N)) = 0.
2. By the area formula and blow-up, F = Φ(ℝⁿ) has approximate tangent plane range(ι + ι'Df(v)) at Φ(v) for v ∉ N.
3. The upper density theorem (localized to sets compactly inside W) shows that the densities of Hⁿ⌞(M ∖ F) and Hⁿ⌞(F ∖ M) vanish Hⁿ-a.e. on M ∩ F ∩ W.
4. Transfer the approximate tangent plane from F to M and conclude by uniqueness of approxTangentPlane.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json  (mode local-project; project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; diff GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean  (both identical)`
- `rg -n -i 'allard|tilt.?excess|harmonic.?approx|lipschitz.?approx' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT`
- `rg -n 'sorry' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch05/Submission.lean; rg -n '^theorem|^lemma' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch05/Submission.lean`
- `rg -l -i "rellich|kondrachov|weyl's lemma|weakly harmonic" /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory  (no match, exit 1)`
- `rg -n 'theorem ae_differentiableAt|theorem norm_fderiv_le_of_lipschitz' Analysis/Calculus/Rademacher.lean Analysis/Calculus/FDeriv/Basic.lean; grep -n ae_differentiableAt Analysis/Calculus/Rademacher.lean  (in the snapshot Mathlib)`
- `rg -n 'theorem exists_disjoint_subfamily_covering_enlargement_closedBall' MeasureTheory/Covering/Vitali.lean; rg -n 'theorem ae_tendsto_average_norm_sub' MeasureTheory/Covering/Differentiation.lean; rg -n 'theorem measurable_fderiv' Analysis/Calculus/FDeriv/Measurable.lean  (in the snapshot Mathlib)`
- `sed -n 10,30p lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter05/Basic.lean (simongmt rev 2b3663083f3fe399b6296fb8eaee52169170e197 from the snapshot's lake-manifest.json)`
- `python3: lean_name collision scan of the 12 dorag_* names over dag.json (200 nodes), nodes/*/*.json and other workspaces' dag.json; exact-statement comparison against .humanize/math-wiki/*.md (43 pages)`
- `python3 -I lean_contract.validate_lean_statement on all 12 lean_statements; lean (lean-4.35.0-rc3, LEAN_PATH of the built workspace) on 13 comparator-format modules Challenge_<key>.lean`
- `lean Check.lean (#check of the Mathlib API used by the assembly); lean Assembly.lean with #print axioms GMT.Ch07.AllardAsmV3.assembly`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Vitali.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter05/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-graph-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-graph-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-graph-a1/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/math-wiki`
- `/tmp/allard-v3-work/v3/Challenge_PARENT.lean`
- `/tmp/allard-v3-work/asm3/Assembly.lean`
- `/tmp/allard-v3-work/asm3/Assembly.log`

The snapshot pins project b4d606d and Mathlib 25730c7c. Its GMT/Ch07/Contract.lean is byte-identical to the workspace contract and to GMT/Ch07/Submission.lean, which is the compiler context of every child type.

Nothing in the snapshot proves Allard regularity or any child:
- The only Allard-related declarations are in GMT/Ch05/Submission.lean: Prop definitions (TiltExcessHeightEstimate, AffineApproximationLemma, LipschitzApproximationLemma, HarmonicApproximationLemma, TiltExcessDecayTheorem, AllardRegularityTheorem, …) for a different varifold type. They are used only in main_theorem := by sorry (line 461), so nothing is proved there.
- SimonGMT Chapter05/Basic.lean says compactness, Lipschitz approximation, excess decay and Allard regularity are not formalized.
- The Rellich/Kondrachov/Weyl/weakly-harmonic search found no match in the snapshot's Mathlib Analysis and MeasureTheory.
The split into 12 children therefore stands, and no identical comparator-approved declaration exists to reuse.

The Mathlib tools the children cite exist at the pinned revision:
- LipschitzWith.ae_differentiableAt (Rademacher.lean:385);
- norm_fderiv_le_of_lipschitz (FDeriv/Basic.lean:947);
- measurable_fderiv (FDeriv/Measurable.lean:378);
- Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall (Vitali.lean:158);
- VitaliFamily.ae_tendsto_average_norm_sub (Differentiation.lean:837).

Lean checks:
- All 12 child types and the frozen parent type elaborate in comparator scope; the only diagnostic is the expected sorry warning.
- The assembly proves the exact parent type from the five top-level child types, with axioms propext, Classical.choice and Quot.sound only.
- No dorag_* name collides with any DAG reservation.
