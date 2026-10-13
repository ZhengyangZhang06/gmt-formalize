# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_transfer-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_transfer-a1.bounded_transfer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Steps 3.2, 4 and 5, the passage from the two-sided comparison (3a) to clauses (a) and (b), abstracted to arbitrary measure spaces. In the parent: X = ℝⁿ, m = Lⁿ, D = B̆_{r/2}(0), Y = ℝ^{n+k}, ν = μ, S = Φ(D), φ(x) = P(x − ξ), c = 2ⁿ, s = Σ_j‖Dfʲ‖². Conventions: ∫⁻ is the lower Lebesgue integral in [0, ∞] and ∫ the Bochner integral. Fix x₀ ∈ X, which exists because X is nonempty.
1. Preliminaries.
 (i) Z is measurable. So ∫⁻_D F dm = ∫⁻_{D∩Z} F dm + ∫⁻_{D∖Z} F dm for every F : X → [0, ∞] (lintegral_inter_add_sdiff), and ∫_D u dm = ∫_{D∩Z} u dm + ∫_{D∖Z} u dm for every u integrable on D (integral_inter_add_sdiff).
 (ii) m(D ∩ Z) ≤ m(Z) ≤ ofReal a < ∞, so (m(D ∩ Z)).toReal ≤ a because a ≥ 0 (ENNReal.toReal_le_of_le_ofReal).
 (iii) Let u : X → ℝ be measurable with |u| ≤ G everywhere. Then u is integrable on D, being bounded with m(D) < ∞ (Measure.integrableOn_of_bounded). Likewise u∘φ is ν-integrable on S: it is measurable because φ is, it is bounded, and ν(S) < ∞.
2. Proof of (a). Let g be measurable with 0 ≤ g ≤ G; then G ≥ g(x₀) ≥ 0. By 1(i), ∫⁻_D ofReal(g) dm = ∫⁻_{D∩Z} ofReal(g) dm + ∫⁻_{D∖Z} ofReal(g) dm.
 - First term. ofReal(g(v)) ≤ ofReal(G) pointwise, so it is ≤ ∫⁻_{D∩Z} ofReal(G) dm = ofReal(G)·m(D∩Z) ≤ ofReal(G)·ofReal(a) = ofReal(G·a). This uses setLIntegral_const, 1(ii), and ENNReal.ofReal_mul with G ≥ 0.
 - Second term. H := ofReal ∘ g is measurable, so the left comparison hypothesis gives ∫⁻_{D∖Z} ofReal(g) dm ≤ ∫⁻_S ofReal(g(φ(y))) dν(y).
 Adding, ∫⁻_D ofReal(g) dm ≤ ofReal(G·a) + ∫⁻_S ofReal(g∘φ) dν. Commuting the sum gives (a).
3. Key estimate. Let h : X → ℝ be measurable with 0 ≤ h ≤ G everywhere, so G ≥ h(x₀) ≥ 0. Let Δ(h) := (∫_S h∘φ dν) − (∫_D h dm). Claim: −G·a ≤ Δ(h) ≤ G·(c·∫_D s dm).
 3.1 Integrability.
 - By 1(iii), h is integrable on D, hence on D ∖ Z, and h∘φ is integrable on S.
 - s·h is integrable on D ∖ Z (Integrable.mono'). It is a.e.-strongly measurable, since s is integrable on D ⊇ D ∖ Z and h is measurable. Also |s·h| = s·h ≤ G·s, and G·s is integrable on D ∖ Z.
 - Hence (1 + c·s)·h = h + c·(s·h) is integrable on D ∖ Z.
 3.2 Comparison of Bochner integrals. Apply the hypothesis to the measurable H := ofReal ∘ h. Using 1 + c·s ≥ 0 (as c, s ≥ 0) and ENNReal.ofReal_mul:
 ∫⁻_{D∖Z} ofReal(h) dm ≤ ∫⁻_S ofReal(h∘φ) dν ≤ ∫⁻_{D∖Z} ofReal(1 + c s)·ofReal(h) dm = ∫⁻_{D∖Z} ofReal((1 + c s)·h) dm.
 For a nonnegative integrable function u on a set, ∫ u = (∫⁻ ofReal(u)).toReal (integral_eq_lintegral_of_nonneg_ae), and ∫⁻ ofReal(u) < ∞ (hasFiniteIntegral_iff_ofReal). By 3.1 this applies to h on D ∖ Z, to h∘φ on S and to (1 + c s)·h on D ∖ Z. Since toReal is monotone on finite values (ENNReal.toReal_mono),
 ∫_{D∖Z} h dm ≤ ∫_S h∘φ dν ≤ ∫_{D∖Z} (1 + c s)·h dm.
 3.3 Lower bound. By 1(i), ∫_D h = ∫_{D∩Z} h + ∫_{D∖Z} h. Also 0 ≤ ∫_{D∩Z} h since h ≥ 0, and ∫_{D∩Z} h ≤ G·(m(D∩Z)).toReal ≤ G·a. The last bound uses norm_setIntegral_le_of_norm_le_const with m(D∩Z) < ∞, then 1(ii) and G ≥ 0. Thus Δ(h) ≥ ∫_{D∖Z} h − ∫_D h = −∫_{D∩Z} h ≥ −G·a.
 3.4 Upper bound. By linearity (integral_add, integral_const_mul), ∫_{D∖Z} (1 + c s)·h = ∫_{D∖Z} h + c·∫_{D∖Z} s·h. Pointwise s·h ≤ G·s, because s ≥ 0 and h ≤ G. So ∫_{D∖Z} s·h ≤ G·∫_{D∖Z} s ≤ G·∫_D s, the last step because s ≥ 0 and D ∖ Z ⊆ D (setIntegral_mono, setIntegral_mono_set). With c ≥ 0 this gives c·∫_{D∖Z} s·h ≤ G·(c·∫_D s). Hence
 Δ(h) ≤ ∫_{D∖Z} h + G·(c ∫_D s) − ∫_D h = −∫_{D∩Z} h + G·(c ∫_D s) ≤ G·(c ∫_D s).
4. Proof of (b). Let g be measurable with |g| ≤ G everywhere; then G ≥ |g(x₀)| ≥ 0. Let g⁺ := max(g, 0) and g⁻ := max(−g, 0). Both are measurable, 0 ≤ g^± ≤ G, and g = g⁺ − g⁻ pointwise (max_zero_sub_max_neg_zero_eq_self). By 1(iii), g^± are integrable on D and g^±∘φ on S, so linearity (integral_sub) gives
 ∫_D g dm = ∫_D g⁺ dm − ∫_D g⁻ dm and ∫_S g∘φ dν = ∫_S g⁺∘φ dν − ∫_S g⁻∘φ dν.
 Therefore (∫_D g dm) − (∫_S g∘φ dν) = Δ(g⁻) − Δ(g⁺). Step 3 applied to h = g⁺ and h = g⁻ gives −G·a ≤ Δ(g^±) ≤ G·(c ∫_D s). Hence
 −(G·a + G·(c ∫_D s)) ≤ Δ(g⁻) − Δ(g⁺) ≤ G·(c ∫_D s) + G·a,
 that is, |(∫_D g dm) − (∫_S g(φ(y)) dν(y))| ≤ G·a + G·(c·∫_D s dm) = G·(a + c·∫_D s dm). This is (b), with the two integrals computed separately and then subtracted. ∎

## Key steps

1. Split D into D ∩ Z and D ∖ Z (Z measurable), and use m(D ∩ Z) ≤ m(Z) ≤ ofReal a with a ≥ 0.
2. (a): the D ∩ Z part is ≤ ofReal(G)·m(Z) ≤ ofReal(G·a); the D ∖ Z part is ≤ ∫⁻_S ofReal(g∘φ) dν by the lower comparison.
3. For measurable 0 ≤ h ≤ G, all relevant integrands are integrable with finite lower integrals, so the comparison passes to Bochner integrals: ∫_{D∖Z} h ≤ ∫_S h∘φ ≤ ∫_{D∖Z}(1 + c s)h.
4. Hence −G·a ≤ Δ(h) := ∫_S h∘φ − ∫_D h ≤ G·c·∫_D s, using 0 ≤ ∫_{D∩Z} h ≤ G·a and ∫_{D∖Z} s h ≤ G ∫_D s.
5. (b): write g = g⁺ − g⁻; linearity gives ∫_D g − ∫_S g∘φ = Δ(g⁻) − Δ(g⁺), whose absolute value is ≤ G(a + c ∫_D s).

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
