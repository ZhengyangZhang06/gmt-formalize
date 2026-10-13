# Parent-supplied natural-language proof

- Parent DAG node: `root.flat_iff_weak-a1.im_series-a1.tsum_tau-a1`
- Child DAG node: `root.flat_iff_weak-a1.im_series-a1.tsum_tau-a1.term_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation:
- H := μHE[n]; L := closure W; K := tsupport ω;
- g(x) := θ(x)·ξ(x)(ω(x)) and G := M.indicator g, so G(x) = g(x) for x ∈ M and G(x) = 0 otherwise;
- ‖·‖ on covectors is the operator norm; ‖·‖ₑ on ℝ is ofReal of the absolute value;
- the hypothesis CompactlyContainedOpen W U says: W is open, L is compact, and L ⊆ U.

1. (g vanishes off W.)
   - If x ∉ K, then ω(x) = 0, since a function vanishes outside its topological support (image_eq_zero_of_notMem_tsupport).
   - Then ξ(x)(ω(x)) = ξ(x)(0) = 0 because ξ(x) is linear, so g(x) = θ(x)·0 = 0.
   - K ⊆ W (hypothesis) and W ⊆ closure W = L. Hence g(x) = 0 for every x ∉ W, and in particular for every x ∉ L.

2. (Null-measurable sets.)
   - M is H-null-measurable (field nullMeasurableSet of the triple).
   - W is open and L is closed, so both are Borel measurable.
   - Hence M ∩ W and M ∩ L are H-null-measurable (NullMeasurableSet.inter).

3. (G = 1_{M∩L}·g.) Let x ∈ ℝ^P.
   - If x ∈ L, then x ∈ M ∩ L ⟺ x ∈ M, so G(x) = (M ∩ L).indicator g (x).
   - If x ∉ L, then g(x) = 0 by step 1, so G(x) = 0 = (M ∩ L).indicator g (x).
   Hence G = (M ∩ L).indicator g.

4. (Measurability of g for ν := H.restrict (M ∩ L).)
   (a) L is compact and L ⊆ U. So field integrableOn (with K := L) gives IntegrableOn θ (M ∩ L) H, i.e. θ is ν-integrable, hence ν-a.e.-strongly measurable.
   (b) ξ is a.e.-strongly measurable for H.restrict M (field aestronglyMeasurable). Since M ∩ L ⊆ M, ν ≤ H.restrict M (Measure.restrict_mono). So ξ is ν-a.e.-strongly measurable (AEStronglyMeasurable.mono_measure).
   (c) ω is continuous, hence ν-a.e.-strongly measurable.
   (d) x ↦ (ξ(x), ω(x)) ∈ NVector (Eucl P) n × Covector (Eucl P) n is ν-a.e.-strongly measurable (AEStronglyMeasurable.prodMk of (b) and (c)). The evaluation map (v, α) ↦ v(α) is bounded bilinear, hence continuous (isBoundedBilinearMap_apply). Composing (Continuous.comp_aestronglyMeasurable), x ↦ ξ(x)(ω(x)) is ν-a.e.-strongly measurable.
   (e) Hence g = θ·(x ↦ ξ(x)(ω(x))) is ν-a.e.-strongly measurable (AEStronglyMeasurable.mul with (a) and (d)).
   Lean note (checked at this pin): (d) is `(isBoundedBilinearMap_apply.continuous : Continuous fun p : NVector (Eucl P) n × Covector (Eucl P) n => p.1 p.2).comp_aestronglyMeasurable (hξ.prodMk hω.aestronglyMeasurable)`. The curried ContinuousLinearMap.apply route fails, because no TopologicalSpace instance is found on `NVector (Eucl P) n →L[ℝ] ℝ`.

5. (First conjunct.) M ∩ L is H-null-measurable (step 2). So aestronglyMeasurable_indicator_iff₀ and step 4 show that (M ∩ L).indicator g is H-a.e.-strongly measurable. By step 3 this function equals G, which proves the first conjunct.

6. (A.e. pointwise bound.)
   - Field orients: for H.restrict M-a.e. x there is an orthonormal τ : Fin n → ℝ^P (the tangent-space clause is not needed here) with ξ(x) = simpleNVector τ or ξ(x) = −simpleNVector τ.
   - M is H-null-measurable, so ae_restrict_iff'₀ turns this into: for H-a.e. x, if x ∈ M then such a τ exists.
   - Fix such an x. We show
     ‖G(x)‖ₑ ≤ (M ∩ W).indicator (y ↦ ofReal(B)·ofReal(θ(y))) (x).   (∗)
   (a) x ∉ M: G(x) = 0, so the left side of (∗) is 0.
   (b) x ∈ M and x ∉ W: g(x) = 0 by step 1, so G(x) = 0 and the left side of (∗) is 0.
   (c) x ∈ M ∩ W: then G(x) = g(x), and the right side of (∗) is ofReal(B)·ofReal(θ(x)).
       - The sibling lemma fiw_ims_tt_unit_bound, applied to τ, w := ξ(x) and α := ω(x), gives |ξ(x)(ω(x))| ≤ ‖ω(x)‖ ≤ B.
       - θ(x) > 0 (field pos), and B ≥ ‖ω(x)‖ ≥ 0.
       - Hence |g(x)| = |θ(x)|·|ξ(x)(ω(x))| = θ(x)·|ξ(x)(ω(x))| ≤ B·θ(x).
       - Therefore ‖G(x)‖ₑ = ofReal|g(x)| (Real.enorm_eq_ofReal_abs) ≤ ofReal(B·θ(x)) (ENNReal.ofReal_le_ofReal) = ofReal(B)·ofReal(θ(x)) (ENNReal.ofReal_mul, since B ≥ 0).
   So (∗) holds for H-a.e. x.

7. (Second conjunct.) By lintegral_mono_ae and step 6:
   ∫⁻ ‖G‖ₑ dH ≤ ∫⁻ (M ∩ W).indicator (y ↦ ofReal(B)·ofReal(θ(y))) dH
     = ∫⁻_{M∩W} ofReal(B)·ofReal(θ) dH   (lintegral_indicator₀; M ∩ W is null-measurable by step 2)
     = ofReal(B)·∫⁻_{M∩W} ofReal(θ) dH   (lintegral_const_mul', since ofReal(B) ≠ ∞).
   This is the second conjunct. ∎

Lean note (checked at this pin):
- Step 3 is a funext with by_cases on x ∈ closure W and x ∈ M, closed by simp.
- Step 2 uses htri.nullMeasurableSet.inter isClosed_closure.measurableSet.nullMeasurableSet and hWo.measurableSet.nullMeasurableSet.
- Step 4(a) uses (htri.integrableOn (closure W) hLc hLU).aestronglyMeasurable.
- Step 4(b) uses htri.aestronglyMeasurable.mono_measure (Measure.restrict_mono inter_subset_left le_rfl).
- In step 6(c), rewrite with indicator_of_mem (show x ∈ M ∩ W from ⟨hxM, hxW⟩).
- Axioms: propext, Classical.choice, Quot.sound.

## Key steps

1. g := θ·ξ(ω) vanishes off tsupport ω ⊆ W ⊆ closure W, so G = 1_{M∩closure W}·g
2. θ (integrable on M ∩ closure W), ξ (restricted from M), ω (continuous) and continuous evaluation make g a.e.-strongly measurable for H⌞(M ∩ closure W); aestronglyMeasurable_indicator_iff₀ then makes G H-a.e.-strongly measurable
3. orients and fiw_ims_tt_unit_bound give |ξ(x)(ω(x))| ≤ ‖ω(x)‖ ≤ B, so ‖G(x)‖ₑ ≤ 1_{M∩W}(x)·ofReal B·ofReal θ(x) for H-a.e. x
4. lintegral_mono_ae, lintegral_indicator₀ and lintegral_const_mul' give ∫⁻‖G‖ₑ ≤ ofReal B·∫⁻_{M∩W} ofReal θ

## Reference use

### local-project

Queries:
- `cat local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `read project GMT/Ch06/Submission.lean (= Contract.lean): IsRectifiableTriple fields subset/nullMeasurableSet/pos/integrableOn/aestronglyMeasurable/orients, tauAction, CompactlyContainedOpen`
- `read SimonGMT Chapter06/Forms.lean (Covector, DifferentialForm, IsTestForm), FormsDuality.lean (NVector, simpleNVector via mkContinuous, simpleNVector_apply), Currents.lean (testFormOnSubmodule, TestFormOn)`
- `rg -n simpleNVector project (only Contract.lean, Submission.lean, README.md); rg -n tauAction project (only Contract.lean, Submission.lean, README.md); rg -n simpleNVector SimonGMT (only Chapter06/FormsDuality.lean); rg 'norm_simpleNVector|simpleNVector_norm|abs_simpleNVector' project+SimonGMT (no match)`
- `rg Mathlib snapshot: exists_open_between_and_isCompact_closure, Continuous.bounded_above_of_compact_support, ContinuousAlternatingMap.le_opNorm, isBoundedBilinearMap_apply, Continuous.comp_aestronglyMeasurable, AEStronglyMeasurable.prodMk, aestronglyMeasurable_indicator_iff₀, ae_restrict_iff'₀, lintegral_mono_ae, lintegral_indicator₀, lintegral_const_mul', Real.enorm_eq_ofReal_abs, integral_tsum, hasSum_integral_of_summable_integral_norm, integral_norm_eq_lintegral_enorm, ENNReal.summable_toReal, ENNReal.tsum_mul_left, integral_indicator₀, integral_const_mul, Set.indicator_mul_right, image_eq_one_of_notMem_mulTSupport, HasFiniteIntegral`
- `python3 -I: all lean_names in dag.json and nodes/*/decomposition-v*.json (282 names; fiw_ims_tt_unit_bound / fiw_ims_tt_term_bound absent); statements of related nodes fiw_imf_simple_dual, fiw_imf_massOn_le, ltg_tau_integrable, iwlp_tau_integrable, polyhedral_approx_ot_tau_mass_le, lpf_simple_nvector_algebra, isoperimetric_abs_covector_apply_le (no identical type)`
- `git archive d8d46c9 into /tmp/tsumtau_decomp.RSBst6 with .lake/packages -> lake-packages-25730c7c; lake build GMT.Ch06.Submission (success)`
- `gmt-compare.py child_modules (mode contract, root GMT.Ch06.main_theorem) + lean_contract.validate_lean_statement on both child types; lake env lean Scratch/Child_fiw_ims_tt_unit_bound.lean, Scratch/Child_fiw_ims_tt_term_bound.lean (only the challenge sorry warning)`
- `lake env lean Scratch/Assembly.lean: #print axioms Submission.fiw_ims_tsum_tau = [propext, sorryAx, Classical.choice, Quot.sound] (sorryAx only from the two child stubs)`
- `lake env lean Scratch/ChildProofs.lean and Scratch/Full.lean: both children proved; parent assembled from them with no sorry; #print axioms = [propext, Classical.choice, Quot.sound]`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Separation/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/GroupWithZero/Indicator.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Group/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Function/L1Space/HasFiniteIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1-tsum-tau-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/tsumtau_decomp.RSBst6/Scratch/Child_fiw_ims_tt_unit_bound.lean`
- `/tmp/tsumtau_decomp.RSBst6/Scratch/Child_fiw_ims_tt_term_bound.lean`
- `/tmp/tsumtau_decomp.RSBst6/Scratch/Assembly.lean`
- `/tmp/tsumtau_decomp.RSBst6/Scratch/ChildProofs.lean`
- `/tmp/tsumtau_decomp.RSBst6/Scratch/Full.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) holds the frozen Ch06 contract.

No project or pinned SimonGMT lemma bounds simpleNVector or the τ-integrand:
- simpleNVector occurs only in FormsDuality.lean (definition, simpleNVector_apply, pushforward) and in the contract's orients field;
- tauAction occurs only in the contract and README;
- searches for norm_simpleNVector, simpleNVector_norm and abs_simpleNVector find nothing.
So the operator-norm unit bound and the single-triple integrand estimate become the two children.

No DAG declaration has an identical type, so fresh names fiw_ims_tt_* are used:
- fiw_imf_simple_dual and polyhedral_approx_ot_tau_mass_le use covectorEuclideanNorm;
- ltg/iwlp_tau_integrable give integrability without the explicit bound;
- lpf_simple_nvector_algebra is a Gram-determinant identity.

Mathlib at this pin supplies every tool cited in the child proofs and the assembly, at the files listed: ContinuousAlternatingMap.le_opNorm (Alternating/Basic.lean:212), isBoundedBilinearMap_apply (BoundedLinearMaps.lean:391), Continuous.comp_aestronglyMeasurable and AEStronglyMeasurable.prodMk (AEStronglyMeasurable.lean:233,256), aestronglyMeasurable_indicator_iff₀ (:558), ae_restrict_iff'₀ (Restrict.lean:624), lintegral_indicator₀ (Lebesgue/Basic.lean:518), lintegral_const_mul' (Lebesgue/Add.lean:420), exists_open_between_and_isCompact_closure (Regular.lean:364), Continuous.bounded_above_of_compact_support (Bounded.lean:153), hasSum_integral_of_summable_integral_norm (DominatedConvergence.lean:96), integral_norm_eq_lintegral_enorm (Bochner/Basic.lean:537), integral_indicator₀ (Bochner/Set.lean:170), ENNReal.summable_toReal (InfiniteSum/ENNReal.lean:350).

Scratch kernel checks:
- both child types elaborate in the comparator's exact child scope;
- the frozen parent type follows from the two child stubs (sorryAx only from the stubs);
- both children are fully proved, and the end-to-end file gives Submission.fiw_ims_tsum_tau with axioms [propext, Classical.choice, Quot.sound] only.
