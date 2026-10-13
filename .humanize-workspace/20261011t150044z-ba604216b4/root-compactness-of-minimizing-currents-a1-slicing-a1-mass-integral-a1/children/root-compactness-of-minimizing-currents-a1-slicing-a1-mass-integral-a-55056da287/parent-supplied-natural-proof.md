# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.slicing-a1.mass_integral-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.slicing-a1.mass_integral-a1.left_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Provenance: Simon Ch. 6, 4.10 and the remark preceding it (chapter-06.txt lines 1367–1376), as used in steps 1–3 and in the liminf comparison of step 4 of the parent node's proof. Here the measure ν of intervals replaces s ↦ μ(W ∩ {a < f < s}), which plays the role of M_W(T⌞{a<f<s}). For ν = f_*(μ⌞W), the function F of step 2 is exactly the parent's F. The proof below is self-contained apart from the sibling theorem cmcs_smi_lintegral_left_dini_le. All integrals are with respect to Lebesgue measure. Write g(t) := liminf_{h→0+} ofReal(h⁻¹)·ν((t − h, t)) (liminf along 𝓝[>] 0) and N := ν((a, b)).
1. (Infinite case.) If N = ∞, the right side is ∞ and the inequality is trivial (le_top). Assume N < ∞.
2. (Distribution function.) For s ∈ ℝ let F(s) := (ν((a, min(s, b)))).toReal.
- Finiteness: (a, min(s, b)) ⊆ (a, b), so ν((a, min(s, b))) ≤ N < ∞ (measure_mono).
- Monotonicity: if s ≤ s′ then min(s, b) ≤ min(s′, b), so (a, min(s, b)) ⊆ (a, min(s′, b)). Both measures are finite, so F(s) ≤ F(s′) (ENNReal.toReal_mono).
- ofReal(F(s)) = ν((a, min(s, b))) for every s (ENNReal.ofReal_toReal).
- F(b) = N.toReal, since min(b, b) = b.
- F(a) = 0, since min(a, b) ≤ a makes (a, min(a, b)) empty.
3. (Strip estimate.) Let t ∈ (a, b) and 0 < h < t − a. Then a < t − h < t < b, so min(t, b) = t and min(t − h, b) = t − h.
- The open intervals (a, t − h) and (t − h, t) are disjoint: points of the first are < t − h, points of the second are > t − h. The second is measurable (measurableSet_Ioo).
- Their union lies in (a, t): x ∈ (a, t − h) gives x < t − h < t, and x ∈ (t − h, t) gives x > t − h > a.
- By additivity and monotonicity (measure_union, measure_mono): ν((a, t − h)) + ν((t − h, t)) ≤ ν((a, t)).
- Since ν((a, t − h)) < ∞: ν((t − h, t)) ≤ ν((a, t)) − ν((a, t − h)) (ENNReal.le_sub_of_add_le_left) = ofReal(F(t)) − ofReal(F(t − h)) = ofReal(F(t) − F(t − h)) (ENNReal.ofReal_sub, using F(t − h) ≥ 0).
- Multiply by ofReal(h⁻¹); multiplication in [0, ∞] is monotone. For h⁻¹ ≥ 0, ofReal(h⁻¹)·ofReal(x) = ofReal(h⁻¹·x) (ENNReal.ofReal_mul). Hence ofReal(h⁻¹)·ν((t − h, t)) ≤ ofReal((F(t) − F(t − h))/h).
4. (Comparison of the liminfs.) Let t ∈ (a, b). Since t − a > 0, the interval (0, t − a) belongs to 𝓝[>] 0 (Ioo_mem_nhdsGT). So the inequality of step 3 holds eventually along 𝓝[>] 0. Hence g(t) ≤ D(t) := liminf_{h→0+} ofReal((F(t) − F(t − h))/h) (Filter.liminf_le_liminf; in the complete lattice [0, ∞] the boundedness side conditions hold automatically).
5. (Integration.) Step 4 holds for every t ∈ (a, b). The lower integral is monotone over the measurable set (a, b) (setLIntegral_mono' with measurableSet_Ioo; no measurability of g or D is needed). So ∫⁻_{(a,b)} g ≤ ∫⁻_{(a,b)} D. The sibling theorem cmcs_smi_lintegral_left_dini_le, applied to the monotone F and a, b, gives ∫⁻_{(a,b)} D ≤ ofReal(F(b) − F(a)). By step 2, this equals ofReal(N.toReal − 0) = N (ENNReal.ofReal_toReal, N < ∞). The case b ≤ a needs no separate argument: step 4 is vacuous and step 5 applies unchanged. ∎

## Key steps

1. If ν((a, b)) = ∞ the bound is trivial. Otherwise F(s) := ν((a, min(s, b))).toReal is monotone, with F(a) = 0 and F(b) = ν((a, b)).toReal.
2. Strip estimate: for t ∈ (a, b) and 0 < h < t − a, ofReal(h⁻¹)·ν((t − h, t)) ≤ ofReal((F(t) − F(t − h))/h), by additivity on the disjoint union (a, t − h) ∪ (t − h, t) ⊆ (a, t).
3. Since (0, t − a) ∈ 𝓝[>] 0, Filter.liminf_le_liminf gives g(t) ≤ D(t) := liminf_{h→0+} ofReal((F(t) − F(t − h))/h) for every t ∈ (a, b).
4. ∫⁻_{(a,b)} g ≤ ∫⁻_{(a,b)} D ≤ ofReal(F(b) − F(a)) = ν((a, b)) (setLIntegral_mono', sibling cmcs_smi_lintegral_left_dini_le, ENNReal.ofReal_toReal).

## Reference use

### local-project

Queries:
- `rg -n 'theorem Monotone.ae_differentiableAt|theorem MonotoneOn.intervalIntegrable_deriv|theorem MonotoneOn.intervalIntegral_deriv_mem_uIcc|Monotone.deriv_nonneg|theorem hasDerivAt_iff_tendsto_slope|tendsto_slope_zero_left|theorem ofReal_integral_eq_lintegral_ofReal|theorem integral_Ioc_eq_integral_Ioo|theorem lintegral_mono_ae|theorem liminf_le_liminf|Tendsto.liminf_eq' local-references/123e8435b4a2469b/mathlib/Mathlib -g '*.lean'`
- `rg -n "theorem setLIntegral_mono'|theorem lintegral_const_mul'|theorem lintegral_congr_ae|theorem le_sub_of_add_le_left|theorem ofReal_sub|theorem ofReal_mul|theorem tendsto_ofReal|Ioo_mem_nhdsGT" local-references/123e8435b4a2469b/mathlib/Mathlib -g '*.lean'`
- `rg -n 'tendsto_neg_nhdsGT_neg|nhdsGT_inv|tendsto_inv_nhdsGT' local-references/123e8435b4a2469b/mathlib/Mathlib (tendsto_neg_nhdsWithin_Ioi absent; tendsto_neg_nhdsGT is the to_additive form of tendsto_inv_nhdsGT)`
- `rg -n "^theorem mul_le_mul_left|^theorem mul_le_mul_right|mul_le_mul_left'" local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean (mul_le_mul_left' absent; mul_le_mul_right (bc : b ≤ c) a : a * b ≤ a * c)`
- `sed -n 1,200p local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean`
- `python3 -I scan of dag.json (642 nodes): lean_name collisions for cmcs_smi_lintegral_ofReal_deriv_le / cmcs_smi_lintegral_left_dini_le / cmcs_smi_lintegral_left_density_le (none); nodes using the same liminf integrand (cmc_fc_good_slice, lcmp_exists_good_slice_level)`
- `for o in 1281 git ref objects: git grep -q -E 'cmcs_smi_|lintegral_left_density_le|lintegral_left_dini_le|lintegral_ofReal_deriv_le' $o -- '*.lean' (0 hits; positive control regcomp_covector_sq_sum_orthonormalBasis: 25 hits)`
- `for r in git refs: git show $r:GMT/Ch07/Submission.lean | grep '^import' (accepted solutions, e.g. dtc_blowUp_density and dtc_mass_eq_measure, add Mathlib imports)`
- `lean GMT/Scratch/cmcs_mass_integral_decomposition/Assembly.lean (3 child stubs + frozen parent; #print axioms: propext, sorryAx, Classical.choice, Quot.sound)`
- `lean GMT/Scratch/cmcs_mass_integral_decomposition/Children.lean (all 3 children + parent fully proved; axioms: propext, Classical.choice, Quot.sound)`
- `lean GMT/Scratch/cmcs_mass_integral_decomposition/TypeCheck.lean (pp.fullNames, pp.coercions, pp.numericTypes, pp.explicit of the child types)`
- `lean GMT/Scratch/cmcs_mass_integral_decomposition/DotCheck.lean ((hF.monotoneOn _).intervalIntegrable_deriv with the extra import)`
- `sed -n 1340,1385p book/chapter-06.txt; grep -n 'is increasing in t|Thus 4.9 gives|^4.10' book/chapter-06.txt`
- `WebSearch: Royden–Fitzpatrick increasing function f' integrable ∫_a^b f' ≤ f(b) − f(a) (https://faculty.etsu.edu/gardnerr/5210/notes/6-2.pdf, Corollary 6.4)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Monotone.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Deriv/Slope.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Instances/ENNReal/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Group/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-slicing-a1-mass-integral-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcs_mass_integral_decomposition/Assembly.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcs_mass_integral_decomposition/Children.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcs_mass_integral_decomposition/TypeCheck.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcs_mass_integral_decomposition/DotCheck.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcs_mass_integral_decomposition/children.json`

Snapshot pins: project b4d606db, Mathlib 25730c7c.

Mathlib (no GMT-specific lemma exists for this node):
- Monotone.ae_differentiableAt, Monotone.deriv_nonneg and HasDerivAt.tendsto_slope_zero_left are already in the frozen import closure.
- Also available: tendsto_neg_nhdsGT (the to_additive form of tendsto_inv_nhdsGT), ENNReal.tendsto_ofReal, Filter.Tendsto.liminf_eq, liminf_le_liminf, setLIntegral_mono', lintegral_const_mul', lintegral_congr_ae, ENNReal.le_sub_of_add_le_left, ENNReal.ofReal_sub, ENNReal.ofReal_mul, ofReal_integral_eq_lintegral_ofReal and integral_Ioc_eq_integral_Ioo.
- MonotoneOn.intervalIntegrable_deriv and MonotoneOn.intervalIntegral_deriv_mem_uIcc live in Mathlib/MeasureTheory/Integral/IntervalIntegral/DerivIntegrable.lean, which is NOT in the closure. Child lebesgue_deriv says to add that import. Accepted solution branches in this run (e.g. dtc_blowUp_density) add Mathlib imports the same way.
- API differences at this revision: mul_le_mul_left' is absent (use mul_le_mul_right), and tendsto_neg_nhdsWithin_Ioi is absent (use tendsto_neg_nhdsGT).

Names and reuse:
- No existing DAG node has an identical statement to reuse.
- The three new cmcs_smi_ names collide with none of the 642 DAG nodes and none of the 1281 git ref objects (the scan was validated by a positive control).
- cmc_fc_good_slice and lcmp_exists_good_slice_level use the same liminf-of-left-density integrand as left_density, so that child is reusable.

Lean checks:
- The child types elaborate after import GMT.Ch07.Submission with no stray coercions (pp.explicit: volume on ℝ, 0 : ℝ, liminf in ℝ≥0∞).
- Assembly.lean proves the byte-identical frozen parent from the three stubs; sorryAx comes only from the stubs.
- Children.lean proves all three children and the parent with only propext, Classical.choice and Quot.sound.

Sources: book chapter-06.txt lines 1367–1376 are the remark and 4.10 that the proofs cite. The public source for Lebesgue's inequality is the ETSU notes on Royden–Fitzpatrick §6.2, Corollary 6.4.
