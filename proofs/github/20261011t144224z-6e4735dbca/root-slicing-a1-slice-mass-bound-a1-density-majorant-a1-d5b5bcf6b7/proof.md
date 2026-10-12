# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_mass_bound-a1`
- Child DAG node: `root.slicing-a1.slice_mass_bound-a1.density_majorant-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Step 5 (5a)–(5d): the measurable majorant and 4.10 of Simon Ch. 6, whose printed argument is “M_W(T⌞{f < t}) is increasing in t, hence is differentiable for L¹-a.e. t and ∫_a^b (d/dt) M_W(T⌞{f < t}) dt ≤ M_W(T⌞{a < f < b}); thus 4.9 gives 4.10”. The statement is the parent's Step 5 for an arbitrary Borel measure ν on ℝ. When the parent applies this lemma, it takes ν := map f (μ_T⌞W), the image under f of μ_T restricted to W. Then ν([t − h, t]) = μ_T(W ∩ {t − h ≤ f ≤ t}), ν((a,b)) = μ_T(W ∩ {a < f < b}) = M_W(R), and ν((a,b) ∩ (−∞, s]) = μ_T(W ∩ {a < f ≤ s}) is the parent's G(s) for s < b. As in the parent, the majorant is the lower left Dini derivative D of G. Step (5a) compares closed and half-open bands, (5b) proves Borel measurability by a rational infimum, and (5d) integrates using Lebesgue's theorem for monotone functions.

Setting. ν is a Borel measure on ℝ (`Measure ℝ`), a < b, and λ is Lebesgue measure on ℝ. For t ∈ ℝ and h > 0 put φ_t(h) := ν([t − h, t])/ofReal(h) ∈ [0,∞] and Λ(t) := liminf_{h→0+} φ_t(h), the liminf along the filter 𝓝[>] 0. Claim: there is a Borel g : ℝ → [0,∞] with Λ(t) ≤ g(t) for every t ∈ (a,b) and ∫⁻_{(a,b)} g dλ ≤ ν((a,b)).

1. (Case Q = ∞.) Put Q := ν((a,b)). If Q = ∞, take g :≡ ∞. It is measurable, Λ(t) ≤ ∞ = g(t) for all t, and ∫⁻_{(a,b)} g dλ ≤ ∞ = Q. From now on assume Q < ∞.

2. (The distribution function G.) For s ∈ ℝ let G(s) := ν((a,b) ∩ (−∞, s]). Since 0 ≤ ν((a,b) ∩ (−∞, s]) ≤ Q < ∞, G(s) is taken as the real number (ν((a,b) ∩ (−∞, s])).toReal. Properties:
 (a) G is nondecreasing, by monotonicity of ν.
 (b) For s′ ≤ s, the set (a,b) ∩ (−∞, s] is the disjoint union of (a,b) ∩ (−∞, s′] and (a,b) ∩ (s′, s]. All measures here are finite, so G(s) − G(s′) = ν((a,b) ∩ (s′, s]).
 (c) G(s) = 0 for s ≤ a, because the set is empty. G(b) = ν((a,b)) = Q.
 (d) G is right-continuous at every s ∈ ℝ. The sets (a,b) ∩ (−∞, r], r > s, decrease as r ↓ s and have finite measure. Their intersection is (a,b) ∩ (−∞, s], since x ≤ r for all r > s forces x ≤ s. By continuity from above (`tendsto_measure_biInter_gt`), G(r) → G(s) as r ↓ s.
 (e) G is Borel measurable, being monotone (`Monotone.measurable`).
 For s < b, G(s) = ν((a, s]) is exactly the parent's G(s).

3. (The functions Δ, D and g.) For t ∈ ℝ and k > 0 put Δ_t(k) := (G(t) − G(t − k))/k. Then Δ_t(k) ≥ 0 by 2(a). Put D(t) := liminf_{k→0+} ofReal(Δ_t(k)) ∈ [0,∞], the liminf along 𝓝[>] 0. Define g(t) := D(t) for t ∈ (a,b) and g(t) := 0 otherwise.

4. ((5a): Λ(t) ≤ D(t) for every t ∈ (a,b).) Fix t ∈ (a,b) and a real c > 1.
 (a) Let 0 < k < t − a and h := k/c ∈ (0, k). Then a < t − k < t − h and t < b, so [t − h, t] ⊆ (a,b) ∩ (t − k, t]. By 2(b),
  ν([t − h, t]) ≤ ν((a,b) ∩ (t − k, t]) = ofReal(G(t) − G(t − k)) = ofReal(k·Δ_t(k)) = ofReal(c·h·Δ_t(k)) = ofReal(c)·ofReal(Δ_t(k))·ofReal(h).
 These are equalities in [0,∞]: G(t) − G(t − k), k·Δ_t(k) = c·h·Δ_t(k) and the factors c, Δ_t(k), h are real numbers ≥ 0, so ofReal is multiplicative on them. Since ofReal(h) is positive and finite, dividing by it gives φ_t(k/c) = ν([t − h, t])/ofReal(h) ≤ ofReal(c)·ofReal(Δ_t(k)) for every k ∈ (0, t − a).
 (b) The map k ↦ k/c sends 𝓝[>] 0 into 𝓝[>] 0. Hence Λ(t) = liminf_{h→0+} φ_t(h) ≤ liminf_{k→0+} φ_t(k/c) (`Filter.Tendsto.liminf_le_liminf_comp`).
 (c) By (a), which holds for all k near 0+, liminf_{k→0+} φ_t(k/c) ≤ liminf_{k→0+} ofReal(c)·ofReal(Δ_t(k)). The constant ofReal(c) is finite, so it factors out of the liminf in [0,∞] (`ENNReal.liminf_const_mul_of_ne_top`), and the bound equals ofReal(c)·D(t).
 (d) Thus Λ(t) ≤ ofReal(c)·D(t) for every c > 1. If D(t) = ∞ the claim is trivial. Otherwise take c = 1 + 1/(n+1) and let n → ∞: ofReal(c)·D(t) → D(t), so Λ(t) ≤ D(t).
 This is the parent's comparison of the closed band {t − h ≤ f ≤ t} with the slightly wider half-open band {t − k < f ≤ t}. Here the width ratio is fixed, k/h = c, instead of k = h + h², and then c ↓ 1.

5. ((5b): D, and hence g, is Borel measurable.)
 (a) (Left-continuity.) Fix t and k₀ > 0. As k ↑ k₀ we have t − k ↓ t − k₀, so G(t − k) → G(t − k₀) by 2(d). Hence Δ_t(k) → Δ_t(k₀) as k → k₀ from the left.
 (b) (Rational infimum.) For every δ > 0,
  inf_{k∈(0,δ)} ofReal(Δ_t(k)) = inf_{q∈ℚ∩(0,δ)} ofReal(Δ_t(q)).
 “≤” holds because ℚ ∩ (0,δ) ⊆ (0,δ). For “≥”, let k ∈ (0,δ) and choose rationals q_n with max(0, k − 1/(n+1)) < q_n < k. Then q_n ∈ (0,δ) and q_n → k from the left. By (a), ofReal(Δ_t(q_n)) → ofReal(Δ_t(k)). Each term is at least the rational infimum, so that infimum is ≤ ofReal(Δ_t(k)).
 (c) (Countable formula.) The intervals (0,δ), δ > 0, form a basis of 𝓝[>] 0, so D(t) = sup_{δ>0} inf_{k∈(0,δ)} ofReal(Δ_t(k)) (`Filter.HasBasis.liminf_eq_iSup_iInf` with `nhdsGT_basis`). The inner infimum decreases as δ grows, and every δ > 0 exceeds some 1/(j+1). Hence, using (b),
  D(t) = sup_{j∈ℕ} inf_{k∈(0,1/(j+1))} ofReal(Δ_t(k)) = sup_{j∈ℕ} inf_{q∈ℚ∩(0,1/(j+1))} ofReal(Δ_t(q)).
 (d) For each fixed q, t ↦ ofReal(Δ_t(q)) = ofReal((G(t) − G(t − q))/q) is Borel by 2(e). Countable infima and suprema of Borel [0,∞]-valued functions are Borel (`Measurable.iInf`, `Measurable.iSup`; for each j and q the inner infimum over the t-independent condition q ∈ (0, 1/(j+1)) is either t ↦ ofReal(Δ_t(q)) or the constant ∞). So D is Borel, and g = 1_{(a,b)}·D is Borel because (a,b) is a Borel set.

6. ((5c): domination.) For t ∈ (a,b), Λ(t) ≤ D(t) = g(t) by step 4.

7. ((5d): integral bound via Lebesgue's theorem.) Write G′ := deriv G. It is the derivative where G is differentiable, and 0 elsewhere by the convention for `deriv`.
 (a) G : ℝ → ℝ is monotone. By Lebesgue's theorem (`Monotone.ae_differentiableAt`), G is differentiable at λ-a.e. s ∈ ℝ.
 (b) Let G be differentiable at s. The slope of G at s along s − k → s gives (G(s) − G(s − k))/k → G′(s) as k → 0+. So ofReal(Δ_s(k)) → ofReal(G′(s)), and D(s) = ofReal(G′(s)), since the liminf of a convergent function is its limit. Hence D = ofReal(G′) λ-a.e.
 (c) G is monotone on [a,b], so `MonotoneOn.intervalIntegrable_deriv` and `MonotoneOn.intervalIntegral_deriv_mem_uIcc` apply (both need `import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable`). They give that G′ is integrable on [a,b] and 0 ≤ ∫_a^b G′ dλ ≤ G(b) − G(a) = Q − 0 = Q, by 2(c). Moreover G′ = deriv G ≥ 0 at every point (`Monotone.deriv_nonneg`): it is a limit of nonnegative difference quotients where G is differentiable, and 0 elsewhere.
 (d) Therefore
  ∫⁻_{(a,b)} g dλ = ∫⁻_{(a,b)} D dλ = ∫⁻_{(a,b)} ofReal(G′) dλ = ofReal(∫_{(a,b)} G′ dλ) = ofReal(∫_a^b G′ dλ) ≤ ofReal(Q) = Q.
 The first equality holds because g = D on (a,b). The second holds by (b) (equality λ-a.e.). The third is `ofReal_integral_eq_lintegral_ofReal`, which applies because G′ is integrable and ≥ 0. The fourth holds because (a,b) and (a,b] differ by a λ-null set.
 G is built from ν restricted to (a,b), so it is real-valued and monotone on all of ℝ. Lebesgue's theorem therefore applies on [a,b] directly. The parent's truncation G̃ to [a′,b′] and its limit a′ ↓ a, b′ ↑ b (monotone convergence) are not needed.

8. (Conclusion.) g is Borel measurable (step 5), Λ(t) ≤ g(t) for every t ∈ (a,b) (step 6), and ∫⁻_{(a,b)} g dλ ≤ ν((a,b)) (step 7). Together with step 1 this proves the claim. ∎

## Key steps

1. If Q = ν((a,b)) = ∞ take g ≡ ∞. Otherwise G(s) := ν((a,b) ∩ (−∞, s]) is real-valued, monotone and right-continuous (continuity from above), with G = 0 on (−∞, a] and G(b) = Q. For s < b it is the parent's G.
2. D(t) := liminf_{k→0+} (G(t) − G(t−k))/k is the lower left Dini derivative; g := D on (a,b) and 0 elsewhere.
3. (5a) [t − k/c, t] ⊆ (a,b) ∩ (t − k, t] gives ν([t−h,t])/h ≤ c·Δ_t(k) with h = k/c. Hence Λ(t) ≤ c·D(t) for every c > 1, so Λ ≤ D = g on (a,b).
4. (5b) Right-continuity of G makes k ↦ Δ_t(k) left-continuous, so D(t) = sup_j inf_{q∈ℚ∩(0,1/(j+1))} Δ_t(q). This is a countable sup/inf of Borel functions, so D and g are Borel.
5. (5d) Lebesgue's theorem (`Monotone.ae_differentiableAt`): D = ofReal(G′) a.e., where G′ = deriv G ≥ 0. With `MonotoneOn.intervalIntegrable_deriv` and `MonotoneOn.intervalIntegral_deriv_mem_uIcc`, ∫⁻_{(a,b)} g = ofReal(∫_a^b G′) ≤ ofReal(G(b) − G(a)) = ν((a,b)).

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean workspaces/gmt-ch06/GMT/Ch06/Submission.lean (identical); cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean (identical)`
- `rg -n 'slicing_mb_' local-references/197bdd4b88278494/project (no match)`
- `rg -n 'theorem norm_deriv_le_of_lipschitz|theorem LipschitzOnWith.extend_real|theorem LipschitzWith.ae_differentiableAt|theorem Monotone.ae_differentiableAt|theorem MonotoneOn.intervalIntegrable_deriv|theorem MonotoneOn.intervalIntegral_deriv_mem_uIcc|theorem liminf_const_mul_of_ne_top|theorem hasDerivAt_integral_of_dominated_loc_of_lip|HasCompactSupport.contDiff_convolution_left|theorem alternatizeUncurryFin_apply|theorem tendsto_measure_biInter_gt|theorem Orthonormal.exists_orthonormalBasis_extension_of_card_eq|theorem fderiv_fun_smul|theorem ofReal_integral_eq_lintegral_ofReal|theorem tendsto_integral_filter_of_dominated_convergence' local-references/197bdd4b88278494/mathlib/Mathlib/{Analysis,Order,MeasureTheory,Topology,LinearAlgebra}`
- `grep -n 'covectorEuclideanNorm|def massAdmissibleOn|def GeometricCurrentOn.massOn|abbrev Covector|abbrev DifferentialForm|def IsTestForm|abbrev exteriorDerivative|abbrev TestFormOn|structure GeometricCurrentOn|boundary_apply|tsupport_exteriorDerivative_subset|abbrev NVector' simongmt/Poincare/SimonGMT/Chapter06/{Mass,Forms,Currents,FormsDuality}.lean`
- `python3 scan of dag.json (200 nodes): lean_name uniqueness of the seven proposed names; search of titles/statements/lean_statements for alternatizeUncurryFin, smulRight, liminf, Monotone, cut-off, mollif, wedge, Dini, McShane, Rademacher (no identical type)`
- `python3 read of nodes/root-slicing-a1-slice-mass-bound-a1/{parent-child-handoff.json, decomposition-v3.json, decomposition-audit-v1..v4.json, decomposition-review-receipt-v1..v4.json}`
- `python3 read of .humanize/swarm-configs/*.json for github_selected_issue 676: 97b6c024c2834d99b1a86982198ed548.json max_nodes=1000 max_depth=6 (older 9bd566bbce374e36839dbfed5b2a4b01.json max_nodes=200)`
- `contract_scope/child_modules in verifier/gmt-compare.py (replayed child scope)`
- `lake env printenv LEAN_PATH; lean -o /tmp/smb_split_v5_bWB45t/out/GMT/Ch06/Submission.olean GMT/Ch06/Submission.lean`
- `lean /tmp/smb_split_v5_bWB45t/check/Stmts.lean (7 child types + parent in the comparator child scope: 0 errors)`
- `lean /tmp/smb_split_v5_bWB45t/check/Instances.lean (wedge degree m+1, operator norms by rfl, C^∞ index)`
- `lean /tmp/smb_split_v5_bWB45t/check/Assembly.lean (#print axioms HumanizeNodeComparator.assembly: [propext, Classical.choice, Quot.sound])`
- `lean /tmp/smb_split_v5_bWB45t/check/Plumbing.lean (dependency instantiations type-check)`
- `lean /tmp/smb_split_v5_bWB45t/check/Names.lean (#check of every lemma cited in the child proofs)`
- `sed -n '1340,1415p' book/chapter-06.txt (Simon Ch. 6, 4.6–4.11)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/FDeriv/Mul.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Order/Filter/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Continuity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1/decomposition-v3.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1/decomposition-audit-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/swarm-configs/97b6c024c2834d99b1a86982198ed548.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/smb_split_v5_bWB45t/check/Stmts.lean`
- `/tmp/smb_split_v5_bWB45t/check/Instances.lean`
- `/tmp/smb_split_v5_bWB45t/check/Assembly.lean`
- `/tmp/smb_split_v5_bWB45t/check/Plumbing.lean`
- `/tmp/smb_split_v5_bWB45t/check/Names.lean`

The pinned snapshot (project d8d46c95, Mathlib 25730c7c) contains the frozen Ch06 contract, and it is byte-identical to the workspace Submission, so child types may use only contract, SimonGMT and Mathlib names. SimonGMT supplies GeometricCurrentOn with boundary ∂T(ω) = T(dω), massOn via covectorEuclideanNorm, TestFormOn, exteriorDerivative (Mathlib's extDeriv, i.e. alternatizeUncurryFin ∘ fderiv) and tsupport_exteriorDerivative_subset. Mathlib supplies McShane extension (LipschitzOnWith.extend_real), Rademacher's theorem (LipschitzWith.ae_differentiableAt), convolution smoothness, differentiation under the integral, Lebesgue's theorem for monotone functions with the integral bound for their derivative, liminf algebra in ℝ≥0∞, dominated convergence along countably generated filters and continuity from above. Every cited name exists at the pinned revision. Neither library contains the sharp cut-off, the wedge coefficient-norm bound, the smooth approximation with an a.e. gradient bound, the slice estimates or the Dini-derivative majorant; these become the seven children. In a scratch compile of the frozen Submission, all seven child types and the parent type elaborate in the comparator's child scope. The exact parent follows from slicing_mass_representation, slicing_representation_unique, slicing_mb_pointwise and slicing_mb_density_majorant with axioms [propext, Classical.choice, Quot.sound], and the dependency instantiations type-check. No proposed name occurs in the snapshot project or among the 200 DAG nodes. The active issue-676 configuration allows 1000 nodes at depth ≤ 6. The printed Simon text (4.9–4.11) matches the supplied proof.
