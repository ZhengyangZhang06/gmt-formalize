# Parent-supplied natural-language proof

- Parent DAG node: `root.bv_results-a1.compactness-a1`
- Child DAG node: `root.bv_results-a1.compactness-a1.convolution_bounds-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon, Introduction to GMT, Ch. 2, Theorem 2.6 (p. 50). The printed proof reduces compactness to precompactness in L¹_loc(U), proved “involving mollification and Arzela's theorem” [GT01, Thm 7.22]; this step supplies the uniform bounds that make the mollified sequence equibounded and equi-Lipschitz. The argument below is step A1(ii) (T1) of the reviewed proof supplied to node root.bv_results-a1.compactness-a1 (Section A of the parent root.bv_results-a1), specialized to this self-contained statement with the details filled in. Notation: ℝⁿ = Rn n = EuclideanSpace ℝ (Fin n), μ = volume (Lebesgue measure), ∫⁻ is the lower Lebesgue integral in [0,∞], ‖a‖ₑ ∈ [0,∞) the extended norm, ofReal = ENNReal.ofReal.

Statement recalled. ρ, F : ℝⁿ → ℝ, A ∈ ℝ with |ρ(x)| ≤ A for all x, K ∈ ℝ≥0 with ρ K-Lipschitz, and F ∈ L¹(ℝⁿ). The convolution is (ρ⋆F)(x) := convolution ρ F (lsmul ℝ ℝ) volume x = ∫ ρ(t) F(x − t) dt (lsmul a b = a · b). Claim, for all x, y: |(ρ⋆F)(x)| ≤ A ∫|F| and |(ρ⋆F)(x) − (ρ⋆F)(y)| ≤ K ‖x − y‖ ∫|F|.

1. ρ is continuous (a Lipschitz map), hence measurable; and A ≥ |ρ(0)| ≥ 0.

2. Swapped form. Lebesgue measure on ℝⁿ is invariant under translations and under x ↦ −x, so the substitution t ↦ z − t gives, for every z, (ρ⋆F)(z) = ∫ ρ(z − t) F(t) dt (Mathlib convolution_lsmul_swap; smul on ℝ is multiplication).

3. Integrability. For every z, the function t ↦ ρ(z − t) F(t) is integrable: F is integrable and t ↦ ρ(z − t) is continuous (hence a.e.-strongly measurable) with |ρ(z − t)| ≤ A for all t (Integrable.bdd_mul).

4. Sup bound. By step 2, |(ρ⋆F)(x)| = |∫ ρ(x − t) F(t) dt| ≤ ∫ A |F(t)| dt = A ∫ |F|, using norm_integral_le_of_norm_le with the integrable majorant t ↦ A|F(t)| (pointwise |ρ(x − t) F(t)| = |ρ(x − t)| |F(t)| ≤ A |F(t)|) and integral_const_mul.

5. Lipschitz bound. By steps 2 and 3 and linearity of the integral (integral_sub), (ρ⋆F)(x) − (ρ⋆F)(y) = ∫ (ρ(x − t) − ρ(y − t)) F(t) dt. For every t, |ρ(x − t) − ρ(y − t)| ≤ K ‖(x − t) − (y − t)‖ = K ‖x − y‖ (LipschitzWith.dist_le_mul), so the integrand has absolute value ≤ K ‖x − y‖ |F(t)|, an integrable majorant. Hence (norm_integral_le_of_norm_le, integral_const_mul) |(ρ⋆F)(x) − (ρ⋆F)(y)| ≤ ∫ K ‖x − y‖ |F(t)| dt = K ‖x − y‖ ∫ |F|. ∎

## Key steps

1. Swap: (ρ⋆F)(z) = ∫ ρ(z − t)F(t) dt (convolution_lsmul_swap; Lebesgue measure is translation and reflection invariant).
2. t ↦ ρ(z − t)F(t) is integrable (bounded continuous times integrable).
3. |∫ρ(x − t)F(t)dt| ≤ ∫A|F| = A∫|F|.
4. (ρ⋆F)(x) − (ρ⋆F)(y) = ∫(ρ(x − t) − ρ(y − t))F(t)dt with |ρ(x − t) − ρ(y − t)| ≤ K‖x − y‖, giving K‖x − y‖∫|F|.

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
