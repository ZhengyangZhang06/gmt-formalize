# Parent-supplied natural-language proof

- Parent DAG node: `root.support_convex_hull-a1.support_in_ball-a1`
- Child DAG node: `root.support_convex_hull-a1.support_in_ball-a1.radial_vanishing-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions. c := R + ε, so c > R ≥ 0. F(x) := nγ(r) + rγ'(r)(1 − q(x)) and G(x) := γ(r)⟨x − ξ, H(x)⟩, so (★★) reads ∫_U F dμ = −∫_U G dμ. The real inner product is symmetric (real_inner_comm), so |⟨H(x), x − ξ⟩| = |⟨x − ξ, H(x)⟩|. U is open (complement of a closed ball), hence measurable; μ⌞U denotes μ restricted to U. Since a Bochner integral of a non-integrable function is 0 by convention, integrability is established (steps 2–5) before linearity is used. This is steps 7–9 of the parent proof, stated for an abstract measure μ (there μ = μ_V) and an abstract function q (there q = q_ξ = V.normalRadialSq ξ); steps 2–5 are the parent's step 7(a)–(d) and steps 6–7 its steps 8–9.

1. Null complement and a bounding ball. E is second countable, hence hereditarily Lindelöf, so the complement of the support of μ is μ-null: μ(E ∖ spt μ) = 0 (Mathlib Measure.support_mem_ae). Since spt μ is compact it is bounded, so there is ρ₀ > 0 with spt μ ⊆ B(ξ, ρ₀) (open ball).

2. Vanishing off S (parent step 7(a)). Let S := spt μ ∩ {x : r(x) ≥ c}. S is compact (a closed subset of the compact set spt μ), S ⊆ U (because r ≥ c > R on S), and μ(S) < ∞ (μ is finite on compact sets). Let x ∈ spt μ ∖ S. Then 0 ≤ r < c, so γ(r) = 0. Moreover rγ'(r) = 0: if r = 0 the factor r vanishes; if 0 < r < c then γ vanishes on the open interval (0, c), which is a neighbourhood of r, so γ'(r) = 0. Hence F(x) = G(x) = γ(r) = rγ'(r)(1 − q(x)) = γ(r)|⟨x − ξ, H(x)⟩| = 0 for every x ∈ spt μ ∖ S. Together with step 1, each of the functions F, G, x ↦ γ(r), x ↦ rγ'(r)(1 − q(x)) and x ↦ γ(r)|⟨x − ξ, H(x)⟩| coincides μ-a.e. with its product with the indicator 1_S.

3. Measurability (parent step 7(b)). γ and γ' are continuous because γ ∈ C¹ (ContDiff.continuous_deriv), x ↦ r(x) is continuous, and q is μ-a.e. strongly measurable. Hence F, x ↦ γ(r) and x ↦ rγ'(r)(1 − q(x)) are μ-a.e. strongly measurable (sums and products of a.e.-strongly measurable real functions).

4. Bounds and integrability of the q-terms (parent step 7(c)). Put M₀ := max_{t ∈ [0, ρ₀]} γ(t) and M₁ := max_{t ∈ [0, ρ₀]} tγ'(t) (continuous functions on a compact interval attain their maxima). For x ∈ S we have 0 ≤ r < ρ₀, hence 0 ≤ γ(r) ≤ M₀ and 0 ≤ rγ'(r) ≤ M₁ (using γ ≥ 0 and γ' ≥ 0 on [0, ∞)), and 0 ≤ 1 − q(x) ≤ 1. With step 2 this gives, μ-a.e., |F| ≤ (nM₀ + M₁)1_S, 0 ≤ γ(r) ≤ M₀1_S and 0 ≤ rγ'(r)(1 − q) ≤ M₁1_S. Since μ(S) < ∞, the functions F, x ↦ γ(r) and x ↦ rγ'(r)(1 − q(x)) are μ-integrable (a.e.-strongly measurable by step 3 and dominated by integrable functions), hence μ⌞U-integrable.

5. Integrability of the H-terms (parent step 7(d)). H is μ-integrable on the compact set S ⊆ U because H is locally integrable on U (Mathlib LocallyIntegrableOn.integrableOn_compact_subset); in particular H is a.e. strongly measurable with respect to μ⌞S, and so are x ↦ ⟨x − ξ, H(x)⟩ (continuous inner product of a.e.-strongly measurable functions), G and x ↦ γ(r)|⟨x − ξ, H(x)⟩|. For x ∈ S, Cauchy–Schwarz gives |⟨x − ξ, H(x)⟩| ≤ r|H(x)|, hence |G(x)| ≤ γ(r)·r·|H(x)| ≤ M₀ρ₀|H(x)| and 0 ≤ γ(r)|⟨x − ξ, H(x)⟩| ≤ M₀ρ₀|H(x)|. So G and x ↦ γ(r)|⟨x − ξ, H(x)⟩| are integrable on S. Since S ⊆ U and both functions vanish μ-a.e. on U ∖ S by step 2, they are μ⌞U-integrable (Mathlib IntegrableOn.of_ae_sdiff_eq_zero).

6. Positivity (parent step 8). By (★★) and linearity of the integral (steps 4 and 5),
n∫_U γ(r) dμ + ∫_U rγ'(r)(1 − q) dμ = ∫_U F dμ = −∫_U G dμ ≤ ∫_U γ(r)|⟨x − ξ, H(x)⟩| dμ,
the inequality because −G(x) ≤ γ(r)|⟨x − ξ, H(x)⟩| for every x (γ(r) ≥ 0 as r ≥ 0). Since rγ'(r)(1 − q(x)) ≥ 0 for every x (r ≥ 0, γ'(r) ≥ 0, q ≤ 1), ∫_U rγ'(r)(1 − q) dμ ≥ 0, and therefore
∫_U γ(r)(n − |⟨H(x), x − ξ⟩|) dμ ≤ 0,
where the integrand is μ⌞U-integrable as the difference of nγ(r) and γ(r)|⟨x − ξ, H(x)⟩|. By (C) and γ(r) ≥ 0 this integrand is ≥ 0 for μ-a.e. x ∈ U. A μ⌞U-integrable function which is ≥ 0 a.e. and has integral ≤ 0 has integral 0 and vanishes a.e. (Mathlib integral_eq_zero_iff_of_nonneg_ae). Hence γ(r)(n − |⟨H(x), x − ξ⟩|) = 0 for μ-a.e. x ∈ U, and since n − |⟨H(x), x − ξ⟩| > 0 for μ-a.e. x ∈ U by (C), γ(|x − ξ|) = 0 for μ-a.e. x ∈ U.

7. Support (parent step 9). The set O := {x : |x − ξ| > c} is open (preimage of (c, ∞) under a continuous map), O ⊆ U because c > R, and γ(|x − ξ|) > 0 for every x ∈ O. By step 6, μ(O) ≤ μ({x ∈ U : γ(|x − ξ|) ≠ 0}) = 0. Every point of spt μ has all its neighbourhoods of positive measure, so the open μ-null set O is disjoint from spt μ (Mathlib Measure.subset_compl_support_of_isOpen). Hence spt μ ⊆ E ∖ O = B_c(ξ) = B_{R+ε}(ξ). ∎

Formalization note (not part of the argument; the numbered steps above are the proof, and either route proves the same statement): steps 2–4 may be shortened by observing that μ(E) = μ(spt μ) + μ(E ∖ spt μ) < ∞, so μ is a finite measure and F, being a.e.-strongly measurable and bounded on spt μ by max_{spt μ}(n|γ(r)| + |rγ'(r)|), is μ-integrable (Integrable.of_bound, IsCompact.exists_bound_of_continuousOn); step 6 may equivalently be run on F + G, which is ≥ γ(r)(n − |⟨x − ξ, H⟩|) + rγ'(r)(1 − q) ≥ 0 μ-a.e. on U and has ∫_U (F + G) dμ = 0 by (★★); step 7 may use Measure.support_subset_of_isClosed with the closed set B_{R+ε}(ξ).

## Key steps

1. μ(E ∖ spt μ) = 0 and spt μ ⊆ B(ξ, ρ₀); S := spt μ ∩ {|x − ξ| ≥ R + ε} is compact, S ⊆ U, μ(S) < ∞
2. On spt μ ∖ S, γ(r) = rγ'(r) = 0, so every integrand vanishes μ-a.e. off S
3. F, γ(r), rγ'(r)(1 − q) are a.e.-strongly measurable and dominated by constants times 1_S, hence μ⌞U-integrable; G and γ(r)|⟨x − ξ, H⟩| are μ⌞U-integrable because H ∈ L¹(S)
4. (★★) and rγ'(r)(1 − q) ≥ 0 give ∫_U γ(r)(n − |⟨H, x − ξ⟩|) dμ ≤ 0 with a.e. nonnegative integrand, so γ(|x − ξ|) = 0 μ-a.e. on U
5. The open set {|x − ξ| > R + ε} ⊆ U is μ-null, hence disjoint from spt μ, so spt μ ⊆ B_{R+ε}(ξ)

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json (project ff75f52a4c9deb3b3abbd91eb31d7b02e29a4cef, mathlib 25730c7c759d108ef87ab70af2342a196760f79d)`
- `sha256sum <snapshot>/project/GMT/Ch04/Contract.lean GMT/Ch04/Contract.lean GMT/Ch04/Submission.lean; git -C <snapshot>/mathlib rev-parse HEAD`
- `rg -n 'lemma support_mem_ae\b|lemma subset_compl_support_of_isOpen|lemma support_subset_of_isClosed|lemma measure_compl_support\b' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `rg -n 'theorem IntegrableOn.of_ae_sdiff_eq_zero|theorem LocallyIntegrableOn.integrableOn_compact_subset|theorem integral_eq_zero_iff_of_nonneg_ae|theorem ContinuousLinearMap.aestronglyMeasurable_comp₂|lemma starProjection_orthogonal.|theorem norm_starProjection_apply_le|theorem contDiff_norm_sq|theorem Filter.EventuallyEq.fderiv_eq|theorem ContDiff.continuous_deriv' <snapshot>/mathlib/Mathlib`
- `rg -n 'protected theorem monotone|theorem zero_of_nonpos|theorem pos_of_pos|theorem nonneg|protected theorem contDiff' <snapshot>/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean; rg -n 'lemma Monotone.deriv_nonneg' <snapshot>/mathlib/Mathlib; rg -n 'theorem one_of_mem_closedBall|protected theorem hasCompactSupport' <snapshot>/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean; rg -n 'theorem abs_real_inner_le_norm' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `rg -n 'AEStronglyMeasurable.inner' <snapshot-equivalent .lake/packages/mathlib>/Mathlib (found only in MeasureTheory/Function/StronglyMeasurable/Inner.lean, not imported by the contract: #check fails in comparator scope)`
- `cat lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/CompactSupportMaximum.lean; rg -n 'support_subset_closedBall_of_radial_lt|integral_eq_zero_iff_of_nonneg_ae|support_mem_ae|support_subset_of_isClosed' that file`
- `python3 -I scan of dag.json lean_names/lean_statements (normalRadialSq, IsTestField, support) and of every nodes/*/decomposition-v*.json and parent-child-handoff.json (reserved names; any stand-alone normalRadialSq measurability statement)`
- `rg -l --no-ignore -F -e exists_radial_cutoff_test_field -e aestronglyMeasurable_normalRadialSq_and_bounds -e support_subset_closedBall_of_radial_identity .humanize GMT simongmt/Poincare mathlib/Mathlib <snapshot>/project (no match)`
- `lake env lean GMT/Ch04/Submission.lean -o /tmp/sib-a1-split/olean/GMT/Ch04/Submission.olean`
- `LEAN_PATH=$(lake env printenv LEAN_PATH):/tmp/sib-a1-split/olean lean /tmp/sib-a1-split/check/{Probe1,Probe2,Assembly1,ChildC1,ChildC2,ChildC3,Final,FinalSorry}.lean`
- `python3 -I verifier/gmt-compare.py contract_scope(Contract.lean, 'GMT.Ch04.main_theorem'); verifier/lean_contract.py validate_lean_statement on the three child statements and the parent statement`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/Deriv/Slope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/ContDiff/Deriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Calculus/FDeriv/Congr.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.lake/packages/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Inner.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/CompactSupportMaximum.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-support-convex-hull-a1-support-in-ball-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-support-convex-hull-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/sib-a1-split/check/Final.lean`
- `/tmp/sib-a1-split/check/FinalSorry.lean`
- `/tmp/sib-a1-split/check/Assembly1.lean`

Snapshot: project ff75f52, mathlib 25730c7c. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean (sha256 6e58e5dd…0f4770b).

The snapshot Mathlib supplies every ingredient the three children need:
- Measure.support_mem_ae, measure_compl_support, subset_compl_support_of_isOpen and support_subset_of_isClosed (Measure/Support.lean).
- Submodule.starProjection_orthogonal' and norm_starProjection_apply_le (Projection/Basic.lean).
- ContDiffBump.one_of_mem_closedBall, hasCompactSupport and contDiff (BumpFunction/Basic.lean).
- expNegInvGlue.contDiff, monotone, nonneg, zero_of_nonpos and pos_of_pos (SmoothTransition.lean).
- Monotone.deriv_nonneg, ContDiff.continuous_deriv, Filter.EventuallyEq.fderiv_eq, contDiff_norm_sq and abs_real_inner_le_norm.
- LocallyIntegrableOn.integrableOn_compact_subset, IntegrableOn.of_ae_sdiff_eq_zero, integral_eq_zero_iff_of_nonneg_ae, ContinuousLinearMap.aestronglyMeasurable_comp₂, Integrable.of_bound and IsCompact.exists_bound_of_continuousOn.

AEStronglyMeasurable.inner is defined only in StronglyMeasurable/Inner.lean, which the contract does not import. The children therefore use continuous_inner.comp_aestronglyMeasurable instead.

The pinned SimonGMT Chapter04/CompactSupportMaximum.lean proves 6.1 only for SimonGMT's own varifold structure, using an expNegInvGlue/smoothTransition profile, integral_eq_zero_iff_of_nonneg_ae and support_subset_of_isClosed. It serves as a pattern only and is not reusable for the contract's RectifiableVarifold.

Nothing is reused from other DAG nodes:
- No declaration in the snapshot, project, SimonGMT or the DAG has any of the three child names (no matches).
- None of the 73 DAG nodes states normalRadialSq measurability on its own. weighted_mono_cutoff_first_variation embeds a restricted version inside a larger conclusion.
- weighted_mono_radial_test_field has different hypotheses: γ is constant near 0 and vanishes beyond b.

Lean checks against a freshly compiled Submission olean, in the comparator scope:
- All three child types elaborate and pass validate_lean_statement.
- All three are proved without sorry.
- The exact frozen parent type is proved from them.
- The comparator targets compile.
- #print axioms reports only propext, Classical.choice and Quot.sound.
