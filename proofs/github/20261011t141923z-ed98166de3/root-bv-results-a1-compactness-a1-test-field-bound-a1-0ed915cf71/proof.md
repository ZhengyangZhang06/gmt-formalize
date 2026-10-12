# Parent-supplied natural-language proof

- Parent DAG node: `root.bv_results-a1.compactness-a1`
- Child DAG node: `root.bv_results-a1.compactness-a1.test_field_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Introduction to GMT, Ch. 2, Theorem 2.6 (p. 50). The printed conclusion includes u ∈ BV_loc(U); this step turns a bound on |Du_k|(W) (Simon 2.4) into the uniform distributional bound of Simon (2.1), which SimonGMT isLocallyBV_of_locallyL1_of_uniform_bound then passes to the L¹_loc limit. The argument below is step A4 of the reviewed proof supplied to node root.bv_results-a1.compactness-a1 (Section A of the parent root.bv_results-a1), specialized to this self-contained statement with the details filled in. Notation: ℝⁿ = Rn n = EuclideanSpace ℝ (Fin n), μ = volume (Lebesgue measure), ∫⁻ is the lower Lebesgue integral in [0,∞], ‖a‖ₑ ∈ [0,∞) the extended norm, ofReal = ENNReal.ofReal.

Statement recalled. W ⊆ ℝⁿ is an arbitrary set, u : ℝⁿ → ℝ arbitrary, c ≥ 0 real with |Du|(W) := Chapter02.bvVariationOn u W ≤ ofReal c, and g ∈ C_c(ℝⁿ, ℝⁿ) (CompactlySupportedContinuousMap) with Chapter02.IsC1TestField g (g is C¹) and tsupport g ⊆ W. Write div g := Chapter02.euclideanDivergence g (the trace of fderiv ℝ g x), s := Chapter02.compactlySupportedSupNorm g = sSup (range fun x ↦ ‖g x‖), and ∫_W for the Bochner integral against μ.restrict W. Claim: ∫_W u · div g ≤ c · s. No integrability of u is needed (Bochner integrals of non-integrable functions are 0 and every identity used below holds unconditionally).

1. g is continuous with compact support, hence bounded (Continuous.bounded_above_of_compact_support): there is C with ‖g x‖ ≤ C for all x. So the set range(x ↦ ‖g x‖) is nonempty and bounded above, and le_csSup gives ‖g x‖ ≤ s for every x. In particular s ≥ ‖g 0‖ ≥ 0.

2. Case s = 0. Then ‖g x‖ ≤ 0, so g x = 0 for all x, i.e. ⇑g is the zero function. Its Fréchet derivative is 0 everywhere, so div g x = trace(0) = 0 for all x. Hence ∫_W u · div g = ∫_W 0 = 0 = c · 0 = c · s.

3. Case s > 0. Let h := s⁻¹ • g ∈ C_c(ℝⁿ, ℝⁿ) (compactly supported continuous maps are closed under scalar multiplication; ⇑h = fun x ↦ s⁻¹ • g x).
 (a) h is C¹ (ContDiff.const_smul applied to the C¹ map g), so Chapter02.IsC1TestField h, and therefore Chapter02.IsLipschitzTestField h by SimonGMT Chapter02.IsC1TestField.isLipschitzTestField (a compactly supported C¹ field is Lipschitz).
 (b) tsupport h ⊆ tsupport g ⊆ W (tsupport_smul_subset_right).
 (c) ‖h x‖ = |s⁻¹| ‖g x‖ = s⁻¹ ‖g x‖. Hence compactlySupportedSupNorm h = sSup (range fun x ↦ s⁻¹ ‖g x‖) = ⨆_x s⁻¹ ‖g x‖ = s⁻¹ · ⨆_x ‖g x‖ = s⁻¹ · s = 1 (Real.mul_iSup_of_nonneg with s⁻¹ ≥ 0). So compactlySupportedSupNorm h ≤ 1.
 (d) g is differentiable at every x (a C¹ map), so fderiv ℝ h x = s⁻¹ • fderiv ℝ g x (fderiv_const_smul, after writing ⇑h = s⁻¹ • ⇑g), and since the trace is linear, div h x = s⁻¹ · div g x for every x.

4. By (a)–(c), h is admissible in the supremum defining |Du|(W), so SimonGMT Chapter02.ofReal_integral_le_bvVariationOn gives ofReal(∫_W u · div h) ≤ |Du|(W) ≤ ofReal c. Since c ≥ 0, ENNReal.ofReal_le_ofReal_iff yields ∫_W u · div h ≤ c.

5. By 3(d), u x · div h x = s⁻¹ · (u x · div g x) for all x, so by integral_const_mul (valid with no integrability assumption) ∫_W u · div h = s⁻¹ · ∫_W u · div g. Thus s⁻¹ · ∫_W u · div g ≤ c, and multiplying by s > 0 (inv_mul_le_iff₀) gives ∫_W u · div g ≤ s · c = c · s. ∎

## Key steps

1. g is bounded, so ‖g(x)‖ ≤ s := compactlySupportedSupNorm g for all x and s ≥ 0.
2. s = 0: g ≡ 0, so div g ≡ 0 and both sides are 0.
3. s > 0: h := s⁻¹•g is a C¹ (hence Lipschitz) C_c field with tsupport h ⊆ W, sup norm s⁻¹·s = 1, and div h = s⁻¹ div g (fderiv_const_smul, linearity of trace).
4. ofReal_integral_le_bvVariationOn: ofReal(∫_W u div h) ≤ |Du|(W) ≤ ofReal c, so ∫_W u div h ≤ c.
5. integral_const_mul: ∫_W u div h = s⁻¹∫_W u div g; multiply by s > 0.

## Reference use

### local-project

Queries:
- `cat local-references/ff09f3909baeeae7/manifest.json (mode local-project; project 1b1689a8deba89d58b36b1a04dba493693824437; mathlib 25730c7c759d108ef87ab70af2342a196760f79d); cmp snapshot project/GMT/Ch02/{Contract.lean,README.md} against the workspace copies (identical)`
- `grep -n 'BV|IsLocallyBV|bvVariation|TendstoLocallyInL1On|IsRelativelyCompactIn' GMT/Ch02/Contract.lean (BVCompactness at lines 240-252)`
- `grep -n 'theorem|lemma|def' simongmt/Poincare/SimonGMT/Chapter02/BV.lean, then a full read`
- `grep -n '2.6|BVCompactness|open W' GMT/Ch02/README.md (row 7; erratum line 87); sed -n 540,630p book/sources/chapter-02-source.txt (printed 2.5-2.6)`
- `grep -n 'theorem|lemma|instance|def ' mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `rg -n 'exists_cthickening_subset_open|IsCompact.cthickening|closure_thickening_subset_cthickening|bounded_above_of_compact_support|ContDiff.lipschitzWith_of_hasCompactSupport|integral_norm_eq_lintegral_enorm|convolution_lsmul_swap|toReal_le_of_le_ofReal' mathlib/Mathlib`
- `grep -rlE 'Kolmogorov.?Riesz|Rellich|Frechet.?Kolmogorov|BoundedVariation.*compact|TotallyBounded.*Lp ' mathlib/Mathlib/{MeasureTheory,Analysis,Topology}; grep -rln mollif mathlib/Mathlib`
- `lean #check batches (Names, Names2, Names3, Sig, Sig2, Sig3, Sig4 .lean) for every lemma cited in the child proofs, e.g. IsOpen.measure_pos, lintegral_add_right, setLIntegral_const, ENNReal.le_div_iff_mul_le, Real.mul_iSup_of_nonneg, fderiv_const_smul, integral_const_mul, Integrable.bdd_mul, norm_integral_le_of_norm_le, finite_cover_balls_of_compact, abs_sub_round, lintegral_add_left', ContinuousOn.aestronglyMeasurable, TotallyBounded.isCompact_of_isClosed, IsCompact.tendsto_subseq, Lp.edist_toLp_toLp, eLpNorm_one_eq_lintegral_enorm, locallyIntegrableOn_iff, Metric.infEDist, Metric.finite_approx_of_totallyBounded; #synth FirstCountableTopology ((j : ℕ) → Lp ℝ 1 (volume.restrict (Q j)))`
- `python3 -I gen_checks.py (verifier gmt-compare.py contract_scope/child_modules + lean_contract.validate_lean_statement), then lean NodeChallenge_00..04.lean against a scratch olean of GMT.Ch02.Submission`
- `python3 -I final_checks.py (AssemblyFinal.lean built from dag.json's lean_statement for root.bv_results-a1.mollifier_estimate-a1 plus the 5 child statements; lean_name scan over dag.json, nodes/*/decomposition-v*.json and every run file), then lean final/AssemblyFinal.lean`
- `lean checks_v1/Truth12.lean, checks_v1/Truth3.lean, prove4/Child4.lean, prove5/Child5.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Normed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Convolution.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Topology/EMetricSpace/BoundedVariation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/BV.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/sources/chapter-02-source.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-bv-results-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-bv-results-a1-compactness-a1/parent-child-handoff.json`
- `/tmp/bvcpt-decomp-tCL0IZ/final/AssemblyFinal.lean`
- `/tmp/bvcpt-decomp-tCL0IZ/final/NodeChallenge_00.lean`
- `/tmp/bvcpt-decomp-tCL0IZ/checks_v1/Truth12.lean`
- `/tmp/bvcpt-decomp-tCL0IZ/checks_v1/Truth3.lean`
- `/tmp/bvcpt-decomp-tCL0IZ/prove4/Child4.lean`
- `/tmp/bvcpt-decomp-tCL0IZ/prove5/Child5.lean`

Contract: the snapshot Contract.lean and README.md are byte-identical to the workspace copies. BVCompactness is the frozen proposition targeted here, and README row 7 / erratum line 87 fix the open-W reading.

SimonGMT: BV.lean supplies the definitions and the A3/A4 library steps: ofReal_integral_le_bvVariationOn, IsC1TestField.isLipschitzTestField, bvVariationOn_le_liminf_of_locallyL1 and isLocallyBV_of_locallyL1_of_uniform_bound. It does not supply subsequence extraction, which README row 7 marks as new.

Mathlib supplies the analytic API: convolution_lsmul_swap, ContDiffBump.normed (needs an extra import of BumpFunction.Normed), the thickening lemmas, Lp completeness, totally bounded ⇒ compact closure, IsCompact.tendsto_subseq, the countable-product FirstCountableTopology instance, finite_cover_balls_of_compact and round/abs_sub_round. It has no L¹ compactness theorem (no Kolmogorov–Riesz/Rellich match; its BoundedVariation file is 1-D eVariationOn) and no mollifier lemma. So children 3–5 are genuine new obligations, and children 1–2 are new SimonGMT-specific lemmas.

Checks:
- All 5 lean_statements validate, and their comparator-generated NodeChallenge modules compile.
- The generated assembly proves BVCompactness from the uncle type and the 5 child types, with axioms [propext, Classical.choice, Quot.sound].
- All 5 children are proved outright in Lean with the same axioms.
- None of the 5 names collides with a reserved declaration.
