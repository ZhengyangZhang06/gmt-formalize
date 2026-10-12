# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_transfer-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_transfer-a1.exceptional_set-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Steps 0.1–0.5, 1 and 2. This keeps the Hⁿ-measure parts of Steps 1.1–1.3 (the bound on Hⁿ(Φ(Z))) and the identity of Step 2. The passage from Hⁿ(Φ(Z)) to Lⁿ(Z) via the graph area formula stays in the parent.
Notation:
- M := R.carrier; θ := R.mult (ℕ-valued), also read as the [0, ∞]-valued density x ↦ (θ(x) : [0, ∞]).
- μ := R.measure = (Hⁿ⌞M).withDensity θ; Hⁿ := μHE[n].
- Φ(v) := ξ + ιv + ι'f(v); D := ball (0 : Euclid n) (r/2); B := closedBall ξ r.
- All integrals are lower Lebesgue integrals.
1. Φ. Since |f(v) − f(w)| ≤ |v − w|, f is 1-Lipschitz, hence continuous. ι and ι' are continuous, so Φ is continuous. For every v, Φ(v) − ξ = ιv + ι'f(v), hence P(Φ(v) − ξ) = P(ιv) + P(ι'f(v)) = v + 0 = v. So Φ is injective. Euclid n is Polish and Φ is continuous and injective, so Φ(A) is Borel for every Borel A ⊆ Euclid n (MeasurableSet.image_of_continuousOn_injOn).
2. Φ(D) ⊆ B. For v ∈ D, |Φ(v) − ξ| = |ιv + ι'f(v)| ≤ |ιv| + |ι'f(v)| = |v| + |f(v)| < r/2 + r/4 ≤ r. This uses that ι, ι' preserve norms and r > 0; orthogonality of ι and ι' is not needed.
3. Formula for μ. For every Borel S, μ(S) = ∫⁻_S θ d(Hⁿ⌞M) = ∫⁻_{S∩M} θ dHⁿ (withDensity_apply, Measure.restrict_restrict). The density x ↦ (θ(x) : [0, ∞]) is measurable: R.mult is measurable (R.measurable_mult), and every map out of ℕ is measurable (measurable_from_nat).
4. First conclusion. B is compact and B ⊆ W ⊆ U. So by step 3 and IMRep.locallyIntegrable_mult, μ(B) = ∫⁻_{M∩B} θ dHⁿ ≠ ∞ (note B ∩ M = M ∩ B). By step 2 and monotonicity, μ(Φ(D)) ≤ μ(B), so μ(Φ(D)) ≠ ∞.
5. The non-unit multiplicity set. Let N := B ∩ {x : θ(x) ≠ 1}, a Borel set (B is closed, θ is measurable). Hypothesis (H1) says μ({x : ¬(x ∈ B → θ(x) = 1)}) = 0 (ae_iff). N is contained in that set, so μ(N) = 0 (measure_mono_null).
6. Hⁿ(N ∩ M) = 0. For x ∈ M, θ(x) ≥ 1: R.mult_pos gives θ(x) > 0, and θ(x) ∈ ℕ. Hence, by step 3 with S = N,
 Hⁿ(N ∩ M) = ∫⁻_{N∩M} 1 dHⁿ ≤ ∫⁻_{N∩M} θ dHⁿ = μ(N) = 0 (setLIntegral_mono).
7. Definition of Z. Let Z := D ∩ Φ⁻¹(Mᶜ ∪ {x : θ(x) ≠ 1}). Z is Borel: D is open, Φ is continuous, M is Borel (R.measurableSet_carrier) and θ is measurable. For v ∈ D: v ∉ Z ⟺ (Φ(v) ∈ M and θ(Φ(v)) = 1).
8. Second conclusion: Hⁿ(Φ(Z)) ≤ ofReal a. Let v ∈ Z and x := Φ(v); then x ∈ B by step 2.
 (i) If x ∈ M, then θ(x) ≠ 1 because v ∈ Z, so x ∈ N ∩ M.
 (ii) If x ∉ M and x ∉ spt μ, then x ∈ (range Φ ∖ spt μ) ∩ B.
 (iii) If x ∉ M and x ∈ spt μ, then x ∈ W (as B ⊆ W), so x ∈ (spt μ ∩ W) ∖ M.
 Thus Φ(Z) ⊆ [(range Φ ∖ spt μ) ∩ B] ∪ [(spt μ ∩ W) ∖ M] ∪ [N ∩ M]. Monotonicity and subadditivity (measure_union_le), together with (H3), (H2) and step 6, give Hⁿ(Φ(Z)) ≤ ofReal a + 0 + 0 = ofReal a.
9. Φ(D ∖ Z) = (Φ(D) ∩ M) ∖ N.
 (⊆) If v ∈ D ∖ Z, then by step 7 Φ(v) ∈ M and θ(Φ(v)) = 1. So Φ(v) ∈ Φ(D) ∩ M and Φ(v) ∉ N.
 (⊇) Let x = Φ(v) with v ∈ D, x ∈ M and x ∉ N. Then x ∈ B (step 2) and x ∉ N, so θ(x) = 1. Hence Φ(v) ∉ Mᶜ ∪ {θ ≠ 1}, i.e. v ∉ Z, and x ∈ Φ(D ∖ Z).
10. Third conclusion. Let h : Euclid (n+k) → [0, ∞] be measurable. Φ(D) is Borel by step 1, so:
 - restriction to Φ(D) commutes with taking the density (restrict_withDensity);
 - (Hⁿ⌞M)⌞Φ(D) = Hⁿ⌞(Φ(D) ∩ M) (Measure.restrict_restrict);
 - integrating against a measure with measurable density multiplies the integrand by the density (lintegral_withDensity_eq_lintegral_mul, θ and h measurable).
 Hence ∫⁻_{Φ(D)} h dμ = ∫⁻_{Φ(D)∩M} θ·h dHⁿ. N is Borel, so split Φ(D) ∩ M into (Φ(D) ∩ M) ∩ N and (Φ(D) ∩ M) ∖ N (lintegral_inter_add_sdiff).
 - The first piece lies in N ∩ M, which is Hⁿ-null by step 6, so its integral is 0 (setLIntegral_measure_zero).
 - On the second piece, which is Borel, θ = 1: a point x there lies in Φ(D) ⊆ B and not in N. So θ·h = h there (setLIntegral_congr_fun).
 Therefore ∫⁻_{Φ(D)} h dμ = ∫⁻_{(Φ(D)∩M)∖N} h dHⁿ = ∫⁻_{Φ(D∖Z)} h dHⁿ by step 9.
11. Steps 4, 7, 8 and 10 give all three conclusions: μ(Φ(D)) ≠ ∞; Z is measurable with Hⁿ(Φ(Z)) ≤ ofReal a; and ∫⁻_{Φ(D)} h dμ = ∫⁻_{Φ(D∖Z)} h dHⁿ for every measurable h ≥ 0. ∎

## Key steps

1. Φ is continuous and injective with P(Φ(v) − ξ) = v, so it maps Borel sets to Borel sets; Φ(D) ⊆ closedBall ξ r by the triangle inequality.
2. μ(S) = ∫⁻_{S∩M} θ dHⁿ for Borel S, so μ(closedBall ξ r) < ∞ by locallyIntegrable_mult, hence μ(Φ(D)) ≠ ∞.
3. N := closedBall ξ r ∩ {θ ≠ 1} has μ(N) = 0 by the multiplicity hypothesis, and Hⁿ(N ∩ M) ≤ μ(N) because θ ≥ 1 on M.
4. Z := D ∩ Φ⁻¹(Mᶜ ∪ {θ ≠ 1}) is Borel, and Φ(Z) ⊆ off-support part ∪ (spt μ ∩ W) ∖ M ∪ (N ∩ M), so Hⁿ(Φ(Z)) ≤ ofReal a.
5. Φ(D ∖ Z) = (Φ(D) ∩ M) ∖ N, and ∫⁻_{Φ(D)} h dμ = ∫⁻_{Φ(D)∩M} θh dHⁿ = ∫⁻_{Φ(D∖Z)} h dHⁿ.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json  (mode local-project; project_commit b4d606db1da5da8fa2c0292ad4924d97de8b3c4b; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean  (both identical)`
- `rg -n -i 'frobenius|hilbert.schmidt|exceptional set|columns_sq|rows_sq|bounded_transfer|graph_measure' <snapshot>/project/GMT --glob '*.lean'`
- `rg -n 'dorag_' <snapshot>/project/GMT --glob '*.lean'  (no match)`
- `rg -n -c 'withDensity|fderiv' <snapshot>/project/GMT --glob '*.lean'; rg -n 'hsNormSq' <snapshot>/project/GMT --glob '*.lean'`
- `rg -n -i 'hilbertSchmidt|hilbert_schmidt' <snapshot>/mathlib/Mathlib/Analysis --glob '*.lean'  (no match)`
- `rg -n per file under <snapshot>/mathlib/Mathlib for the headers of: norm_fderiv_le_of_lipschitz, fderiv_zero_of_not_differentiableAt, measurable_fderiv, toDual_symm_apply, EuclideanSpace.norm_eq, EuclideanSpace.inner_single_right, withDensity_apply, restrict_withDensity, lintegral_withDensity_eq_lintegral_mul, MeasurableSet.image_of_continuousOn_injOn, lintegral_inter_add_sdiff, setLIntegral_const, setLIntegral_mono, setLIntegral_congr_fun, setLIntegral_measure_zero, integral_inter_add_sdiff, norm_setIntegral_le_of_norm_le_const, setIntegral_mono_set, integral_eq_lintegral_of_nonneg_ae, hasFiniteIntegral_iff_ofReal, Measure.integrableOn_of_bounded, max_zero_sub_max_neg_zero_eq_self, ENNReal.toReal_le_of_le_ofReal, measurable_from_nat, measure_ball_lt_top`
- `sed -n 56,95p <snapshot>/project/GMT/Ch07/Contract.lean  (IMRep fields and IMRep.measure)`
- `grep -o 'dorag_tes_gt_[A-Za-z0-9_]*' over workspaces/*/.humanize/github-theorem-prover/runs/*/dag.json (8 DAGs) and this run's nodes/`
- `python3 -I /tmp/gt-v2/scripts/gen.py: verifier/lean_contract.validate_lean_statement and verifier/gmt-compare.py child_modules (contract mode, root GMT.Ch07.main_theorem) on the 3 child types`
- `lean (lean-4.35.0-rc3, LEAN_PATH of the built workspace via /tmp/gt-v2/env.sh) on /tmp/gt-v2/lean/{ProofA,ProofB,ProofC,Asm,Challenge_A,Challenge_B,Challenge_C,Combined,Inst}.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Dual.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/L1Space/HasFiniteIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/Group/MinMax.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-2560155dcc/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-2560155dcc/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-2560155dcc/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/gt-v2/scripts/gen.py`
- `/tmp/gt-v2/out/subproblems-v2.json`
- `/tmp/gt-v2/lean/ProofA.lean`
- `/tmp/gt-v2/lean/ProofB.lean`
- `/tmp/gt-v2/lean/ProofC.lean`
- `/tmp/gt-v2/lean/Asm.lean`
- `/tmp/gt-v2/lean/Combined.lean`
- `/tmp/gt-v2/lean/Inst.lean`
- `/tmp/gt-v2/lean/Challenge_A.lean`
- `/tmp/gt-v2/lean/Challenge_B.lean`
- `/tmp/gt-v2/lean/Challenge_C.lean`

The snapshot pins project b4d606d and Mathlib 25730c7c. Its GMT/Ch07/Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean, so every type was checked in the correct compiler context.

Nothing in the snapshot proves any child, so there is no identical comparator-approved declaration to reuse:
- The project search hits are only Hilbert–Schmidt prose and the definition hsNormSq in GMT/Ch05/Contract.lean:47 and Submission.lean:47, a Ch05-only definition with no lemmas.
- dorag_ has no match in project/GMT.
- hilbertSchmidt has no match in Mathlib/Analysis.

The IMRep fields the proofs use are present at Contract.lean:61-74: measurableSet_carrier, measurable_mult, mult_pos and locallyIntegrable_mult. IMRep.measure, at line 88, is (μHE[n].restrict carrier).withDensity mult.

Every cited Mathlib lemma is present in the snapshot.
Calculus and inner-product lemmas:
- fderiv_zero_of_not_differentiableAt, FDeriv/Basic.lean:234
- norm_fderiv_le_of_lipschitz, FDeriv/Basic.lean:947
- measurable_fderiv, FDeriv/Measurable.lean:378
- toDual_symm_apply, Dual.lean:178
- EuclideanSpace.norm_eq, PiL2.lean:145
- EuclideanSpace.inner_single_right, PiL2.lean:322
Measure lemmas:
- withDensity_apply, WithDensity.lean:44
- restrict_withDensity, WithDensity.lean:215
- lintegral_withDensity_eq_lintegral_mul, WithDensity.lean:398
- MeasurableSet.image_of_continuousOn_injOn, Polish/Basic.lean:821
- measurable_from_nat, Constructions.lean:80
- measure_ball_lt_top, Typeclasses/Finite.lean:373
Lebesgue-integral lemmas (Lebesgue/Basic.lean):
- setLIntegral_const:121, setLIntegral_mono:246, setLIntegral_congr_fun:298, setLIntegral_measure_zero:478, lintegral_inter_add_sdiff:637
Bochner-integral lemmas:
- integral_inter_add_sdiff, Bochner/Set.lean:114
- norm_setIntegral_le_of_norm_le_const, Bochner/Set.lean:613
- setIntegral_mono_set, Bochner/Set.lean:737
- integral_eq_lintegral_of_nonneg_ae, Bochner/Basic.lean:515
- hasFiniteIntegral_iff_ofReal, HasFiniteIntegral.lean:101
- Measure.integrableOn_of_bounded, IntegrableOn.lean:716
Other:
- max_zero_sub_max_neg_zero_eq_self, referenced by an alias at MinMax.lean:27
- ENNReal.toReal_le_of_le_ofReal, Basic/ENNReal/Real.lean:283

Lean results:
- All 3 child types validate and elaborate in comparator scope.
- Each child is proved outright with propext, Classical.choice and Quot.sound only. The only warnings are deprecations: ContinuousLinearMap.zero_apply, Set.mem_setOf_eq, ContinuousLinearMap.lipschitz.
- The exact frozen parent type follows from the 3 child types plus the frozen graph_area type, with standard axioms only.

No dorag_tes_gt_* name is reserved in any DAG.
