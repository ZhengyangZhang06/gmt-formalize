# Parent-supplied natural-language proof

- Parent DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_transfer-a1`
- Child DAG node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1.graph_transfer-a1.jacobian_row_norms-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof Step 3.1, the comparison t(v) ≤ s(v) of the two Hilbert–Schmidt expressions for Df(v), where t(v) = Σ_i|Df(v)e_i|² and s(v) = Σ_j‖Dfʲ(v)‖². It is stated here for an arbitrary map f; no Lipschitz hypothesis is needed. Notation is as in the statement. |·| is the Euclidean norm on Euclid m = EuclideanSpace ℝ (Fin m), and u_i is the i-th coordinate of u ∈ Euclid m.
1. Squared norm in coordinates. For every m ∈ ℕ and u ∈ Euclid m, |u|² = Σ_{i∈Fin m} u_i². Indeed |u| = √(Σ_i |u_i|²) (EuclideanSpace.norm_eq). The radicand is ≥ 0 and |u_i|² = u_i², so squaring gives the claim (Real.sq_sqrt).
2. Squared norm of a functional. For every continuous linear ψ : Euclid n → ℝ, ‖ψ‖² = Σ_{i∈Fin n} ψ(e_i)². Let u := (InnerProductSpace.toDual ℝ (Euclid n)).symm ψ be the Riesz representative of ψ.
 - ⟨u, x⟩ = ψ(x) for every x (InnerProductSpace.toDual_symm_apply).
 - |u| = ‖ψ‖, because toDual is a linear isometry equivalence.
 - The i-th coordinate is u_i = ⟨u, e_i⟩ = ψ(e_i), since EuclideanSpace.inner_single_right gives ⟨u, single i 1⟩ = 1·u_i.
 By step 1, ‖ψ‖² = |u|² = Σ_i u_i² = Σ_i ψ(e_i)².
3. Case 1: f is not differentiable at v. Then Df(v) = 0 (fderiv_zero_of_not_differentiableAt), so each term |Df(v)e_i|² = |0|² = 0 and the left side is 0. The right side is a finite sum of squares, hence ≥ 0. So the inequality holds.
4. Case 2: f is differentiable at v; put L := Df(v). For each j ∈ Fin k, proj_j := EuclideanSpace.proj j is continuous linear, so it has derivative proj_j at every point. By the chain rule, fʲ = proj_j ∘ f is differentiable at v with Dfʲ(v) = proj_j ∘ L.
 - In Lean: HasFDerivAt.comp applied to (EuclideanSpace.proj j : Euclid k →L[ℝ] ℝ).hasFDerivAt and hf.hasFDerivAt, then HasFDerivAt.fderiv.
 - The type ascription fixes the scalar field ℝ, because EuclideanSpace.proj is declared as a StrongDual.
 Consequently Dfʲ(v)(e_i) = (L e_i)_j for all i ∈ Fin n and j ∈ Fin k.
5. By step 2 with ψ = Dfʲ(v), and by step 4, ‖Dfʲ(v)‖² = Σ_{i∈Fin n} ((L e_i)_j)². Sum over j ∈ Fin k and exchange the two finite sums (Finset.sum_comm):
 Σ_j ‖Dfʲ(v)‖² = Σ_i Σ_j ((L e_i)_j)² = Σ_i |L e_i|²,
 the last equality by step 1 with u = L e_i ∈ Euclid k. So in Case 2 the two sides are equal, and in particular the inequality holds.
6. Steps 3 and 5 cover all cases, so Σ_{i∈Fin n} |Df(v)e_i|² ≤ Σ_{j∈Fin k} ‖Dfʲ(v)‖² for every f and v. ∎

## Key steps

1. Squared norms in Euclid m are sums of squared coordinates.
2. Via the Riesz representative, ‖ψ‖² = Σ_i ψ(e_i)² for every functional ψ on Euclid n.
3. If f is not differentiable at v, then Df(v) = 0, so the left side is 0 ≤ right side.
4. If f is differentiable at v, the chain rule gives Dfʲ(v) = proj_j ∘ Df(v).
5. Exchanging the finite sums gives Σ_j‖Dfʲ(v)‖² = Σ_iΣ_j((Df(v)e_i)_j)² = Σ_i|Df(v)e_i|².

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
