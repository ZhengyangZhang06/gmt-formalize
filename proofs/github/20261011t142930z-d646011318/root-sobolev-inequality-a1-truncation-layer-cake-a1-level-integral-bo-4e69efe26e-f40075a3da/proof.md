# Parent-supplied natural-language proof

- Parent DAG node: `root.sobolev_inequality-a1.truncation_layer_cake-a1.level_integral_bound-a1`
- Child DAG node: `root.sobolev_inequality-a1.truncation_layer_cake-a1.level_integral_bound-a1.layer_cake-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. E = Ambient n ℓ = ℝ^{n+ℓ} with its Borel σ-algebra. For A ⊆ E, μ[A] ∈ [0, ∞] is the measure of A and μ(A) = μ.real A is its real value (the toReal of μ[A]). ∫ denotes Bochner integrals (0 for non-integrable integrands) and ∫⁻ lower Lebesgue integrals of [0, ∞]-valued functions. ofReal : ℝ → [0, ∞] is y ↦ max(y, 0), dt is Lebesgue measure on ℝ, and x^y is the real power Real.rpow (used only with bases x ≥ 0). Source: step 8 of the parent proof (Simon 4.11 with α = n/(n − 1) and t₀ = ε, used on the last page of the proof of Simon 5.7), with the parts of parent steps 1 and 3 that it uses. Here the shift t ↦ t + ε is carried out inside the one-dimensional inner integral; this is equivalent to the parent's translation of the outer integral. Notation: b := 1/(n − 1), p := n/(n − 1), K₀ := tsupport h, f(x) := max(h(x) − ε, 0), g(t) := (t + ε)^b.

1. (Exponents.) As a real number n ≥ 2, so n − 1 > 0. Hence b > 0, p = n/(n − 1) = 1/(n − 1) + 1 = b + 1 > 0, and 1/p = (n − 1)/n.
2. (Sets.) Since h is continuous, each M_s is open, hence Borel. For s > 0, x ∈ M_s gives h(x) > s > 0, so x ∈ support h ⊆ K₀. K₀ is compact, so μ[M_s] ≤ μ[K₀] < ∞. Hence ofReal(μ(M_s)) = μ[M_s] for s > 0.
3. (Rewriting the integrand.) Fix t > 0. Then t + ε > 0, so g(t) = (t + ε)^b ≥ 0 and ofReal(g(t)·μ(M_{t+ε})) = ofReal(g(t))·ofReal(μ(M_{t+ε})) = ofReal(g(t))·μ[M_{t+ε}] by step 2. Moreover {x : t < f(x)} = M_{t+ε}: since t > 0, t < max(h(x) − ε, 0) holds iff t < h(x) − ε, i.e. iff t + ε < h(x). Therefore the left side equals L := ∫⁻_{(0,∞)} μ[{x : t < f(x)}]·ofReal(g(t)) dt.
4. (Tonelli / layer cake.) f is continuous, hence measurable, and f ≥ 0. g is continuous: Real.continuous_rpow_const with exponent b ≥ 0, and on [0, ∞) the base t + ε ≥ ε > 0. Hence g is integrable on every interval [0, T], and g ≥ 0 on (0, ∞). Write μ[{f > t}] = ∫⁻ 1_{t < f(x)} dμ(x). The function (x, t) ↦ 1_{t < f(x)} ofReal(g(t)) is measurable on E × ℝ, and μ is σ-finite (finite on compact sets in the σ-compact space E). So Tonelli's theorem gives L = ∫⁻ (∫⁻_{(0,∞)} 1_{t < f(x)} ofReal(g(t)) dt) dμ(x) = ∫⁻ (∫⁻_{(0, f(x))} ofReal(g(t)) dt) dμ(x). Since g is continuous and ≥ 0 on [0, f(x)], the inner lower integral is ofReal(∫_0^{f(x)} g(t) dt). Thus L = ∫⁻ ofReal(∫_0^{f(x)} g(t) dt) dμ(x). This is exactly Mathlib's layer-cake formula lintegral_comp_eq_lintegral_meas_lt_mul for these f and g.
5. (Inner integral.) Fix x. Substitute u = t + ε (intervalIntegral.integral_comp_add_right) and apply the power rule for the exponent b > −1 (integral_rpow): ∫_0^{f(x)} (t + ε)^b dt = ∫_ε^{f(x)+ε} u^b du = ((f(x) + ε)^{b+1} − ε^{b+1})/(b + 1). If h(x) > ε, then f(x) + ε = h(x) and b + 1 = p, so this equals (h(x)^p − ε^p)/p = (1/p)(h(x)^p − ε^p). If h(x) ≤ ε, then f(x) = 0 and the integral over [0, 0] is 0. Hence ofReal(∫_0^{f(x)} g) = 1_{M_ε}(x)·ofReal((1/p)(h(x)^p − ε^p)) for every x.
6. (Restriction to M_ε.) M_ε is measurable, so by steps 3–5, L = ∫⁻ 1_{M_ε}(x) ofReal((1/p)(h(x)^p − ε^p)) dμ(x) = ∫⁻_{M_ε} ofReal((1/p)(h^p − ε^p)) dμ.
7. (Back to a Bochner integral.) x ↦ (1/p)(h(x)^p − ε^p) is continuous (p > 0), so it is integrable on the compact set K₀ ⊇ M_ε, hence on M_ε. On M_ε it is ≥ 0: there h(x) > ε > 0, and y ↦ y^p is nondecreasing on [0, ∞), so h(x)^p ≥ ε^p. For a function integrable and nonnegative on M_ε, the lower integral of ofReal of it equals ofReal of its integral. Hence L = ofReal(∫_{M_ε} (1/p)(h^p − ε^p) dμ) = ofReal((1/p)·∫_{M_ε} (h^p − ε^p) dμ) = ofReal(((n − 1)/n)·∫_{M_ε} (h^p − ε^p) dμ), using 1/p = (n − 1)/n from step 1. Together with step 3 this is the claimed identity. ∎

## Key steps

1. b := 1/(n−1) > 0, p = b + 1 > 0, 1/p = (n−1)/n; μ[M_s] < ∞ for s > 0 since M_s ⊆ tsupport h
2. For t > 0: ofReal((t+ε)^b μ(M_{t+ε})) = μ[{f > t}]·ofReal((t+ε)^b), with f := max(h − ε, 0) and {f > t} = M_{t+ε}
3. Tonelli (layer cake): ∫⁻_{(0,∞)} μ[{f>t}] ofReal(g(t)) dt = ∫⁻ ofReal(∫_0^{f(x)} g) dμ, with g(t) = (t+ε)^b
4. ∫_0^{f(x)} (t+ε)^b dt = 1_{M_ε}(x)(h(x)^p − ε^p)/p, by substitution u = t + ε and the power rule
5. (h^p − ε^p)/p is integrable and ≥ 0 on M_ε, so the lower integral equals ofReal(((n−1)/n)∫_{M_ε}(h^p − ε^p) dμ)

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json`
- `sha256sum <snapshot>/project/GMT/Ch04/Contract.lean GMT/Ch04/Contract.lean GMT/Ch04/Submission.lean`
- `rg -n 'theorem lintegral_comp_eq_lintegral_meas_lt_mul\b' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Layercake.lean`
- `rg -n 'theorem lintegral_rpow_eq_lintegral_meas_lt_mul' <snapshot>/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Integral.lean`
- `rg -n over <snapshot>/mathlib/Mathlib for 'theorem lintegral_lintegral_swap\b|theorem ofReal_integral_eq_lintegral_ofReal\b|theorem integral_rpow\b|theorem integral_deriv_eq_sub\b|theorem integral_comp_add_right\b|theorem integral_comp_sub_left\b|theorem Integrable.bdd_mul\b|theorem integrable_indicator_iff\b|theorem setIntegral_mono_on\b|theorem setIntegral_mono_set\b|theorem mul_rpow\b|theorem rpow_mul\b|lemma Monotone.deriv_nonneg\b|theorem lintegral_const_mul'|bounded_above_of_compact_support|SigmaFinite.of_isFiniteMeasureOnCompacts'`
- `lean Avail.lean / Names.lean: #check of the above lemmas after `import GMT.Ch04.Submission`, plus `example ... [IsFiniteMeasureOnCompacts μ] : SFinite μ := inferInstance``
- `cat lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/{LayerCake,SobolevTruncation}.lean; grep -n 'theorem layerCake_rpow|theorem lintegral_deriv_shifted_cutoff|theorem lintegral_tail_weight|theorem lintegral_smooth_truncation_energy_le' -r .../Chapter04`
- `grep -n '4.11' book/chapter-04.txt; sed -n 560,600p book/chapter-04.txt; sed -n 800,880p book/chapter-04.txt`
- `git show <accepted candidate commits>:GMT/Ch04/Submission.lean | grep '^import' (import policy across all humanize-recursive branches)`
- `python3 -I scope.py (verifier gmt-compare.contract_scope) and gen.py (lean_contract.validate_lean_statement + gmt-compare.child_modules(mode=contract))`
- `lake env lean GMT/Ch04/Submission.lean -o /tmp/slib-audit/olean/GMT/Ch04/Submission.olean`
- `LEAN_PATH=$(lake env printenv LEAN_PATH):/tmp/slib-audit/olean lean /tmp/slib-audit/lean/{Challenge_<name>,Assembly,ProofA,ProofB,ProofC}.lean and /tmp/slib-audit/verify/Combined.lean (#print axioms)`
- `for each proposed name: grep -c <name> dag.json; git grep -l <name> on all 331 refs; grep -rl <name> .humanize .swarm-worktrees; grep -rn <name> SimonGMT`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-sobolev-inequality-a1-truncation-layer-cake-a1-level-integral-bound-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-sobolev-inequality-a1-truncation-layer-cake-a1-level-integral-bound-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Layercake.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Integral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/VectorMeasure/SetIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/Deriv/Slope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/LayerCake.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/SobolevTruncation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/slib-audit/lean/Assembly.lean`
- `/tmp/slib-audit/lean/ProofA.lean`
- `/tmp/slib-audit/lean/ProofB.lean`
- `/tmp/slib-audit/lean/ProofC.lean`
- `/tmp/slib-audit/lean/Challenge_sobolev_level_moment_factor.lean`
- `/tmp/slib-audit/lean/Challenge_sobolev_level_energy_tonelli.lean`
- `/tmp/slib-audit/lean/Challenge_sobolev_level_layer_cake.lean`
- `/tmp/slib-audit/verify/Combined.lean`
- `/tmp/slib-audit/draft/subproblems.json`

Contract provenance. The snapshot Contract.lean, the workspace Contract.lean and the workspace Submission.lean are byte-identical (sha256 6e58e5dd…0f4770b). The manifest pins project ff75f52 and Mathlib 25730c7c.

Mathlib lemmas. Everything the children need is in the snapshot and reachable from `import GMT.Ch04.Submission`, so no new imports are needed:
- lintegral_comp_eq_lintegral_meas_lt_mul (Layercake.lean:478), used for (iii) with f = max(h−ε, 0) and g(t) = (t+ε)^{1/(n−1)};
- lintegral_lintegral_swap (Prod.lean:1071);
- ofReal_integral_eq_lintegral_ofReal (Bochner/Basic.lean:739);
- integral_rpow;
- intervalIntegral.integral_deriv_eq_sub, integral_comp_add_right, integral_comp_sub_left;
- Integrable.bdd_mul, integrable_indicator_iff;
- setIntegral_mono_on, setIntegral_mono_set;
- Real.mul_rpow, Real.rpow_mul;
- Monotone.deriv_nonneg (Deriv/Slope.lean:191);
- lintegral_const_mul' (Lebesgue/Add.lean:420);
- Continuous.bounded_above_of_compact_support;
- the instance SigmaFinite.of_isFiniteMeasureOnCompacts (SFinite.lean:701), so SFinite μ is inferred.

SimonGMT and existing declarations. Pinned SimonGMT Chapter04 has layerCake_rpow, lintegral_tail_weight and lintegral_deriv_shifted_cutoff (equal to (B1)). They are not imported by Submission and are not needed. Its moment lemma superlevel_rpow_mass_le_compact_moment is tied to its own RectifiableVarifold and integrates over tsupport h, so it cannot be reused. No existing declaration (DAG, any branch, SimonGMT) matches any of the three child statements.

Source text. Simon pp. 99–100 (book/chapter-04.txt lines 800–880) and 4.11 (lines 573–590) confirm the source structure: weight by (t+ε)^{1/(n−1)}, the trivial moment inequality, integration over t ∈ (0, ∞), then 4.11.

Lean checks of the children:
- Each child type passes validate_lean_statement and elaborates in a comparator-generated contract-scope challenge file.
- Assembly.lean proves the frozen parent type, byte-identical to dag.json, from the three sorry'd children.
- ProofA/B/C and Combined.lean prove all three child types and the parent with zero sorry; #print axioms shows only [propext, Classical.choice, Quot.sound].
- An independent reviewer reproduced the build, checked statement bytes and Iff.rfl parses, and ACCEPTED.

Name collisions. The proposed names have no collisions anywhere (no match in dag.json, 331 refs, .humanize, swarm worktrees or SimonGMT).
