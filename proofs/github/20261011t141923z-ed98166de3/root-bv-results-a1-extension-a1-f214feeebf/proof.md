# Parent-supplied natural-language proof

- Parent DAG node: `root.bv_results-a1`
- Child DAG node: `root.bv_results-a1.extension-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Introduction to GMT, Ch. 2, Lemma 2.8 (pp. 51–53). Printed proof (cleaned transcription, as in the parent): “Assume R = 1, ξ = 0. Let d(x) = dist(x, ∂U). Since U is convex, U_σ = {x : dist(x,∂U) > σ} is convex for each σ ≥ 0 […] and 0 < d(x) < d(y) ⇒ (y − x)·Dd(x) ≥ 0 for all x ∈ U at which d is differentiable. Since B_δ(0) ⊆ U and |Dd(x)| = 1 at points of differentiability in U, taking y = −δDd(x) gives (1) x·Dd(x) ≤ −δ for a.e. x ∈ U with d(x) < dist(B_δ(0), ∂U). Let γ : ℝ → [0,1] be increasing, C¹, γ(t) = 0 for t ≤ σ/2, γ(t) = 1 for t ≥ σ, and (2) φ = γ∘d. Then (3) δ|Dφ(x)| ≤ −x·Dφ(x). By definition of |Dw|, (4) ∫|D(φu)| ≤ ∫|Dφ||u| + ∫ φ|Du|, and by (3) (5) δ∫|Dφ||u| ≤ −∫ x·Dφ |u| = ∫ |u| div(xφ) … ≤ ∫_U |D|u|| + n∫|u| ≤ ∫_U |Du| + n∫|u| (because |D|u|| ≤ |Du| by 2.5 and lower semicontinuity). Finally ∫_{ℝⁿ}|Du| ≤ liminf ∫|D(φu)| since φu → u in L¹, and 2.8 follows from (4), (5).”
Readings (GMT/Ch02/README.md): spt u ⊂ Ū means u = 0 a.e. off Ū, and ∫_{ℝⁿ}|Du| = ∫_Ū|Du| is encoded as |Du|(ℝⁿ∖Ū) = 0. As in the parent, the printed cut-off argument is kept, but the final limit is taken directly on test fields (no product lower semicontinuity). The cut-offs are Lipschitz, built from a piecewise-linear γ and level sets of d chosen to be null. The complete argument below is Section C of the parent proof. The inequality |D|u||(U) ≤ |Du|(U) is the sibling theorem Submission.bv_abs_variation_le.

Notation. E := ℝⁿ = EuclideanSpace ℝ (Fin n), μ := volume. |Dv|(A) := Chapter02.bvVariationOn v A. div g := Chapter02.euclideanDivergence g = trace Dg, with Dg := fderiv ℝ g (0 at points of non-differentiability). A field g ∈ C_c(E,E) is admissible for an open set A if it is Lipschitz (IsLipschitzTestField), tsupport g ⊆ A and compactlySupportedSupNorm g ≤ 1; then ‖g(x)‖ ≤ 1 for all x (le_csSup on the bounded range). By SimonGMT ofReal_integral_le_bvVariationOn, ofReal(∫_A v div g) ≤ |Dv|(A) for every admissible g. Recall also: div g is Borel (measurable_euclideanDivergence), |div g| ≤ nΛ for a Λ-Lipschitz g (norm_euclideanDivergence_le_of_lipschitz), div g = 0 off tsupport g (support_euclideanDivergence_subset), and Lipschitz maps on E are differentiable a.e. (Rademacher, LipschitzWith.ae_differentiableAt).

Choice of constant. Given n and δ ∈ (0,1), put C := max(1 + δ⁻¹, nδ⁻¹) ≥ 1 > 0. Let U, R, ξ, u satisfy the hypotheses: u ∈ L¹(E), |Du|(E) < ∞, and u = 0 a.e. on E ∖ closure U.

C0. |Du|(E ∖ closure U) = 0. The set A := (closure U)ᶜ is open and measurable. For g admissible for A: since u = 0 μ-a.e. on A (ae_restrict_iff' applied to the hypothesis), the integrand u·div g vanishes (volume.restrict A)-a.e., so ∫_A u div g = 0 and the term is ofReal 0 = 0. A supremum of zeros is 0. This proves the first conjunct (for every n).

Case n = 0. E is a single point, so U = E (it contains ξ) and |Du|(E) = |Du|(U). Since C ≥ 1, |Du|(E) ≤ ofReal C·|Du|(U) ≤ ofReal C·(|Du|(U) + ofReal R⁻¹·∫⁻_U ‖u‖ₑ). From now on n ≥ 1, so U ≠ E (U is bounded) and Uᶜ ≠ ∅.
Reduction. If |Du|(U) = ∞, the right side of the second conjunct is ∞, because ofReal C ≠ 0. Assume M_U := (|Du|(U)).toReal with |Du|(U) = ofReal M_U < ∞, and put A_U := ∫_U |u| < ∞ (so ofReal A_U = ∫⁻_U ‖u‖ₑ).

C1. The distance function. d(x) := infDist(x, Uᶜ).
 (a) d is 1-Lipschitz, d = 0 off U, and d > 0 on U (U open).
 (b) d is concave on U. Let x, y ∈ U, t ∈ (0,1), z := (1 − t)x + ty and s := (1 − t)d(x) + t d(y) > 0. Recall ball(x, d(x)) ⊆ U and ball(y, d(y)) ⊆ U. For ‖a‖ < s put a_x := a·d(x)/s and a_y := a·d(y)/s. Then (1 − t)a_x + t a_y = a, ‖a_x‖ < d(x) and ‖a_y‖ < d(y), so z + a = (1 − t)(x + a_x) + t(y + a_y) ∈ U by convexity. Hence ball(z,s) ⊆ U and d(z) ≥ s.
 (c) If x ∈ U and d is differentiable at x, then ‖Dd(x)‖ = 1. Indeed ‖Dd(x)‖ ≤ 1 since d is 1-Lipschitz. Conversely, Uᶜ is closed and nonempty and E is proper, so there is a ∈ Uᶜ with ‖x − a‖ = d(x) > 0 (IsClosed.exists_infDist_eq_dist). With e := (a − x)/‖a − x‖ and 0 ≤ s ≤ d(x), we get d(x + se) ≤ ‖x + se − a‖ = d(x) − s. Hence Dd(x)[e] ≤ −1 and ‖Dd(x)‖ ≥ 1.

C2. Key geometric inequality. Let η₀ := min{d(y) : y ∈ closedBall(ξ,δR)} > 0; this is a continuous positive function on a nonempty compact subset of U. Claim: if x ∈ U, d is differentiable at x and d(x) < η₀, then −Dd(x)[x − ξ] > δR.
 Proof. Let ν ∈ E be the gradient of d at x, so Dd(x)[h] = ⟨ν,h⟩ and ‖ν‖ = 1 by C1(c). Put w := ξ − δRν. Then w ∈ closedBall(ξ,δR) ⊆ U, so d(w) ≥ η₀ > d(x).
 The segment [x,w] lies in U, and φ(t) := d(x + t(w − x)) is concave on [0,1] by C1(b), with φ'(0) = Dd(x)[w − x]. For a concave φ the slope (φ(t) − φ(0))/t is nonincreasing in t ∈ (0,1], so φ(1) − φ(0) ≤ φ'(0). Hence
   0 < d(w) − d(x) ≤ ⟨ν, w − x⟩ = ⟨ν, ξ − x⟩ − δR‖ν‖² = −Dd(x)[x − ξ] − δR.

C3. Cut-offs.
 (a) Null level sets. For c > 0 the level sets {d = c} are pairwise disjoint measurable subsets of U, and μ(U) < ∞. So the set B of c > 0 with μ({d = c}) > 0 is countable (Mathlib Measure.countable_meas_pos_of_disjoint_iUnion). Choose ε_j ∈ (0, min(η₀, 1/(j + 1))) with ε_j ∉ B and ε_j/2 ∉ B; this is possible since the excluded set B ∪ 2B is countable. So ε_j → 0, ε_j < η₀, and μ({d = ε_j}) = μ({d = ε_j/2}) = 0.
 (b) The cut-off. For ε > 0 let γ_ε(t) := min{1, max{0, 2t/ε − 1}}; it is (2/ε)-Lipschitz, takes values in [0,1], equals 0 for t ≤ ε/2 and 1 for t ≥ ε. Put φ_ε := γ_ε ∘ d. Then:
 - φ_ε is (2/ε)-Lipschitz and 0 ≤ φ_ε ≤ 1;
 - φ_ε = 0 on {d ≤ ε/2}, so tsupport φ_ε ⊆ {d ≥ ε/2}, a closed bounded subset of U, hence compact;
 - φ_ε = 1 on {d ≥ ε};
 - φ_ε(x) → 1_U(x) as ε → 0 for every x: for x ∈ U, φ_ε(x) = 1 as soon as ε ≤ d(x); for x ∉ U, d(x) = 0 so φ_ε(x) = 0.
 (c) The a.e. inequality. Fix ε = ε_j and consider the open sets A₁ := {d < ε/2}, A₂ := {ε/2 < d < ε} and A₃ := {d > ε}. They cover E up to the μ-null set {d = ε/2} ∪ {d = ε}.
 - On A₁ and on A₃, φ_ε is locally constant, so Dφ_ε = 0 there.
 - On A₂, φ_ε = (2/ε)d − 1, so at every x ∈ A₂ where d is differentiable (a.e. by Rademacher), Dφ_ε(x) = (2/ε)Dd(x) (derivatives of functions agreeing near x coincide). For such x we have x ∈ U and d(x) < ε < η₀, so C1(c) and C2 give δR‖Dφ_ε(x)‖ = (2/ε)δR ≤ (2/ε)(−Dd(x)[x − ξ]) = −Dφ_ε(x)[x − ξ].
 Hence for μ-a.e. x:
   δR‖Dφ_ε(x)‖ ≤ −Dφ_ε(x)[x − ξ].   (C3)

C4. Key bound: for ε = ε_j, ∫ |u|‖Dφ_ε‖ ≤ δ⁻¹M_U + nδ⁻¹R⁻¹A_U.
 (a) The field V(x) := φ_ε(x)(x − ξ)/R.
 - V is Lipschitz. If φ_ε(x) ≠ 0 then x ∈ U ⊆ closedBall(ξ,R), and V(x) − V(y) = φ_ε(y)(x − y)/R + (φ_ε(x) − φ_ε(y))(x − ξ)/R, so ‖V(x) − V(y)‖ ≤ (1/R + 2/ε)‖x − y‖. The case φ_ε(y) ≠ 0 is symmetric, and if both vanish then V(x) = V(y) = 0.
 - tsupport V ⊆ tsupport φ_ε ⊆ U is compact, and ‖V(x)‖ ≤ φ_ε(x)‖x − ξ‖/R ≤ 1.
 So −V (an element of C_c(E,E)) is admissible for U.
 (b) At every x where φ_ε is differentiable (a.e.), DV(x)[h] = (φ_ε(x)h + Dφ_ε(x)[h](x − ξ))/R, so div V(x) = (nφ_ε(x) + Dφ_ε(x)[x − ξ])/R. Hence a.e. −Dφ_ε(x)[x − ξ] = nφ_ε(x) − R div V(x).
 (c) By (C3), a.e. |u|‖Dφ_ε‖ ≤ (δR)⁻¹|u|(nφ_ε − R div V). All these functions are integrable: u ∈ L¹, and φ_ε, Dφ_ε, div V are bounded and measurable. So
   ∫ |u|‖Dφ_ε‖ ≤ (δR)⁻¹(n∫|u|φ_ε − R∫|u| div V).
 (d) First term: ∫|u|φ_ε ≤ ∫_U |u| = A_U, since 0 ≤ φ_ε ≤ 1_U.
 (e) Second term. div(−V) = −div V everywhere (fderiv(−V) = −fderiv V), and div V = 0 off tsupport V ⊆ U. So
   −∫|u| div V = ∫_U |u| div(−V) ≤ (|D|u||(U)).toReal,
 by ofReal_integral_le_bvVariationOn applied to the function |u| and the admissible field −V. By the sibling theorem Submission.bv_abs_variation_le (O := U open; u is integrable on E, hence locally integrable on U), |D|u||(U) ≤ |Du|(U) = ofReal M_U < ∞. So −∫|u| div V ≤ M_U.
 Therefore ∫|u|‖Dφ_ε‖ ≤ (δR)⁻¹(nA_U + R M_U) = δ⁻¹M_U + nδ⁻¹R⁻¹A_U.

C5. Bound on |Du|(E). Let g be admissible for E = univ, Λ-Lipschitz. By iSup_le it suffices to prove ∫_E u div g ≤ C(M_U + R⁻¹A_U); note ∫ x in univ, … = ∫ x, … (Measure.restrict_univ).
 (a) Dominated convergence. φ_{ε_j} u div g → 1_U u div g pointwise (C3(b)), with dominating function nΛ|u| ∈ L¹. Also 1_U u = u a.e.: u = 0 a.e. off closure U, and closure U ∖ U = frontier U is μ-null for convex U (Mathlib Convex.addHaar_frontier). Hence ∫ u div g = lim_j ∫ φ_{ε_j} u div g.
 (b) Fix j and ε = ε_j.
 - φ_ε g is Lipschitz, being the product of two bounded Lipschitz functions; tsupport(φ_ε g) ⊆ tsupport φ_ε ⊆ U is compact; ‖φ_ε g‖ ≤ 1. So φ_ε g is admissible for U.
 - At every x where both φ_ε and g are differentiable (a.e., Rademacher), D(φ_ε g)(x)[h] = φ_ε(x)Dg(x)[h] + Dφ_ε(x)[h]·g(x). Hence div(φ_ε g)(x) = φ_ε(x) div g(x) + Dφ_ε(x)[g(x)], since the trace of h ↦ Dφ_ε(x)[h]·g(x) is Dφ_ε(x)[g(x)].
 - All integrands are integrable (u ∈ L¹, the other factors bounded measurable). So
   ∫ φ_ε u div g = ∫ u div(φ_ε g) − ∫ u Dφ_ε[g] ≤ ∫_U u div(φ_ε g) + ∫|u|‖Dφ_ε‖,
 using ‖g‖ ≤ 1, and ∫ u div(φ_ε g) = ∫_U u div(φ_ε g) because div(φ_ε g) vanishes off U.
 - Admissibility gives ofReal(∫_U u div(φ_ε g)) ≤ |Du|(U) = ofReal M_U, so ∫_U u div(φ_ε g) ≤ M_U.
 - With C4: ∫ φ_ε u div g ≤ M_U + δ⁻¹M_U + nδ⁻¹R⁻¹A_U ≤ C(M_U + R⁻¹A_U).
 (c) Letting j → ∞ in (a) gives ∫_E u div g ≤ C(M_U + R⁻¹A_U). Since C, M_U, R⁻¹, A_U ≥ 0,
   ofReal(∫_E u div g) ≤ ofReal C·(ofReal M_U + ofReal R⁻¹·ofReal A_U) = ofReal C·(|Du|(U) + ofReal R⁻¹·∫⁻_U ‖u‖ₑ).
 Taking the supremum over g gives bvVariationOn u univ ≤ ofReal C·(bvVariationOn u U + ofReal R⁻¹·∫⁻ x in U, ‖u x‖ₑ). Together with C0 this proves BVExtensionEstimate with C = max(1 + δ⁻¹, nδ⁻¹). ∎

## Key steps

1. C = max(1 + 1/δ, n/δ); C0: |Du|((closure U)ᶜ) = 0 because u = 0 a.e. there; n = 0 trivial; assume |Du|(U) < ∞.
2. C1–C2: d = dist(·,Uᶜ) is concave on U with |∇d| = 1 where differentiable; the supergradient inequality at w = ξ − δR∇d(x) gives −(x − ξ)·∇d(x) > δR when d(x) < η₀.
3. C3: choose ε_j ↓ 0 with null level sets; Lipschitz cut-offs φ_ε = γ_ε∘d satisfy δR|∇φ_ε| ≤ −(x − ξ)·∇φ_ε a.e. and φ_ε → 1_U.
4. C4: with the admissible field −V, V = φ_ε(x − ξ)/R, and Submission.bv_abs_variation_le, get ∫|u||∇φ_ε| ≤ δ⁻¹|Du|(U) + nδ⁻¹R⁻¹∫_U|u|.
5. C5: for each test field g, the a.e. product rule div(φ_ε g) = φ_ε div g + ∇φ_ε·g, admissibility of φ_ε g for U, C4, and dominated convergence (frontier of convex U is null) give ∫u div g ≤ C(|Du|(U) + R⁻¹∫_U|u|).

## Reference use

### local-project

Queries:
- `rg -n 'theorem (normed_neg|integral_normed|nonneg_normed|support_normed_eq|tsupport_normed_eq|hasCompactSupport_normed|contDiff_normed|continuous_normed)' mathlib/Mathlib/Analysis/Calculus/BumpFunction/`
- `rg -n 'contDiff_convolution_left|contDiff_convolution_right|hasFDerivAt_convolution_right' mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `rg -n 'convolution_tendsto_right' mathlib/Mathlib; rg -n 'notation.*convolution' mathlib/Mathlib/Analysis/Convolution.lean`
- `rg -in 'eLpNorm.*convolution|convolution.*eLpNorm|lintegral.*convolution|young' mathlib/Mathlib; rg -iln 'mollif' mathlib/Mathlib`
- `rg -n 'exists_hasCompactSupport' mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `rg -n 'theorem (integral_lineDeriv_mul_eq|ae_lineDeriv_sum_eq|ae_differentiableAt)' mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `rg -n 'def (infEdist|infEDist|infDist|cthickening|thickening)' mathlib/Mathlib/Topology/MetricSpace`
- `rg -n 'exists_cthickening_subset_open|exists_infDist_eq_dist|lineDeriv_eq_fderiv|addHaar_frontier|countable_meas_pos_of_disjoint|lintegral_lintegral_swap|integral_comp_comm|support_convolution_subset|lipschitzWith_of_hasCompactSupport|exists_contDiff_tsupport_subset|exists_contMDiffMap_one_nhds_of_subset_interior' mathlib/Mathlib`
- `grep -n 'theorem|def' simongmt/Poincare/SimonGMT/Chapter02/BV.lean, then a full read of BV.lean`
- `grep -n 'BV|2.6|2.7|2.8|open' project/GMT/Ch02/README.md; cmp project/GMT/Ch02/Contract.lean against the workspace GMT/Ch02/Contract.lean; rg -n 'Submission.|namespace Submission' project --glob '*.lean'`
- `lean Avail.lean: #check convolution, ContDiffBump, HasCompactSupport.contDiff_convolution_left, Metric.infDist, Metric.infEDist, lineDeriv, LipschitzWith.ae_differentiableAt, LipschitzWith.integral_lineDeriv_mul_eq, Convex.addHaar_frontier, gradient, Integrable.exists_hasCompactSupport_lintegral_sub_le after import GMT.Ch02.Submission`
- `python3 -I gen_checks.py (verifier gmt-compare.py contract_scope and child_modules plus lean_contract.validate_lean_statement), then lean on NodeChallenge_00..07.lean, AssemblyCheck.lean and Sanity.lean against a scratch olean of GMT.Ch02.Submission`
- `grep -rl for each of the 8 proposed lean_names in the run directory; list lean_name of every dag.json node and every nodes/*/decomposition-v1.json subproblem`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/Rademacher.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/LineDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/HausdorffDistance.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Convex/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-bv-results-a1/parent-child-handoff.json`
- `/tmp/bvdecomp-tYsCkA/checks/NodeChallenge_00.lean`
- `/tmp/bvdecomp-tYsCkA/checks/NodeChallenge_07.lean`
- `/tmp/bvdecomp-tYsCkA/checks/AssemblyCheck.lean`
- `/tmp/bvdecomp-tYsCkA/checks/Sanity.lean`
- `/tmp/bvdecomp-tYsCkA/checks/Avail.lean`

The snapshot Contract.lean is byte-identical to the workspace contract and defines BVCompactness, BVPoincare and BVExtensionEstimate exactly as split. README rows 7–9 and the errata at lines 87 and 94–95 match the readings used: open W in 2.6; u ∈ L¹ in 2.7; and in 2.8, u = 0 a.e. off Ū with the conclusion encoded as |Du|(ℝⁿ∖Ū) = 0. The pinned SimonGMT BV.lean supplies the definitions and every lemma cited: euclideanDivergence_eq_sum_inner, measurable_euclideanDivergence, norm_euclideanDivergence_le_of_lipschitz, support_euclideanDivergence_subset, ofReal_integral_le_bvVariationOn, IsC1TestField.isLipschitzTestField, bvVariationOn_le_liminf_of_locallyL1, isLocallyBV_of_locallyL1_of_uniform_bound and isLocallyBV_zero. The snapshot Mathlib supplies the analytic tools: ContDiffBump.normed (contDiff_normed, nonneg_normed, support_normed_eq, integral_normed), HasCompactSupport.contDiff_convolution_left/right, hasFDerivAt_convolution_right, support_convolution_subset, LipschitzWith.integral_lineDeriv_mul_eq, LipschitzWith.ae_differentiableAt, DifferentiableAt.lineDeriv_eq_fderiv, Integrable.exists_hasCompactSupport_lintegral_sub_le, IsCompact.exists_cthickening_subset_open, IsClosed.exists_infDist_eq_dist, Convex.addHaar_frontier and Measure.countable_meas_pos_of_disjoint_iUnion. Mathlib has no lemma for L¹ convergence of mollifiers (no 'mollif' match and no convolution lemma with eLpNorm or lintegral), and no BV compactness, Poincaré or extension theorem, so those are genuine new obligations. In the frozen import closure, ContDiffBump.normed, gradient, Convex.addHaar_frontier and Integrable.exists_hasCompactSupport_lintegral_sub_le are unavailable (unknown field or constant). The child statements therefore use only convolution, kernel hypotheses that avoid ContDiffBump, fderiv, ball/closedBall and SimonGMT names; child proofs may add Mathlib imports to the Submission, which the verifier permits. With the comparator's own scope replay and statement validator, all 8 lean_statements elaborate and all 8 generated NodeChallenge modules compile. Sanity.lean confirms that normed ContDiffBumps satisfy the kernel hypotheses and that convolution ρ F (lsmul ℝ ℝ) volume x = ∫ t, ρ t * F (x - t). The assembly ⟨Submission.bv_compactness_theorem, Submission.bv_poincare_theorem, Submission.bv_extension_estimate_theorem⟩ type-checks against the selected type; apart from the sorry placeholders, it depends only on propext, Classical.choice and Quot.sound. The project snapshot has no Submission.* declarations, and neither dag.json nor any node file mentions the 8 proposed names, so none of them collides with a reserved declaration.
