# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.weighted_from_unweighted-a1`
- Child DAG node: `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.weighted_from_unweighted-a1.closed_piece_tangent-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 4–10 of the parent proof, i.e. Simon Ch. 3, Remark 1.8(1): for x ∈ M_j ∖ E, if T_x M_j exists as in Def. 1.4 then T_x M exists as in Def. 1.7 and T_x M = T_x M_j. The integrals are transported to the original side of the blow-up. Parent steps 6, 8 and 9 are the siblings ball_mass_bound, tail_vanish and freeze_weight; parent step 5 is the sibling blowup_cov.

Notation: Hⁿ := μHE[n]; η_r := blowUpMap x r, so η_r(z) = r⁻¹(z − x); μ' := (Hⁿ⌞A).withDensity(‖ϑ‖ₑ). For f ∈ C_c(ℝ^{n+ℓ}, ℝ) and r > 0 put:
- I(r) := ∫_{η_r(A)} f(y)ϑ(x + r y) dHⁿ(y);
- T(r) := ∫_{η_r(C)} f dHⁿ;
- E₁(r) := (rⁿ)⁻¹∫_C f(η_r(z))(ϑ(z) − ϑ(x)) dHⁿ(z);
- E₂(r) := (rⁿ)⁻¹∫_{A∖C} f(η_r(z))ϑ(z) dHⁿ(z).

1. Dimension. The first conjunct of HasWeightedApproximateTangentSpaceAt n A ϑ x P is finrank P = n, which is the first conjunct of HasApproximateTangentSpaceAt n C x P. Fix f ∈ C_c(ℝ^{n+ℓ}, ℝ); it remains to show I(r) → ϑ(x)∫_P f dHⁿ as r → 0 in 𝓝[>] 0.

2. Finiteness. Hⁿ(C) ≤ Hⁿ(A) < ∞, since C ⊆ A.

3. Three limits as r → 0 in 𝓝[>] 0.
(a) ϑ(x)·T(r) → ϑ(x)·∫_P f dHⁿ: apply the second conjunct of HasApproximateTangentSpaceAt n C x P to f and multiply by the constant ϑ(x) (Tendsto.const_mul).
(b) E₁(r) → 0: apply freeze_weight to C, ϑ, x and f, with C Borel, Hⁿ(C) < ∞ (step 2) and ContinuousWithinAt ϑ C x. Its bounded-density hypothesis (∀ R > 0, ∃ Λ, eventually (rⁿ)⁻¹Hⁿ.real(C ∩ B_{rR}(x)) ≤ Λ) is exactly the conclusion of ball_mass_bound applied to C, x, P, which uses Hⁿ(C) < ∞ and T_x C = P.
(c) E₂(r) → 0: apply tail_vanish with S := A ∖ C, ϑ integrable on A, and f. S is Borel because A and C are Borel, and S ⊆ A. Its hypothesis (ρⁿ)⁻¹μ'.real((A ∖ C) ∩ B_ρ(x)) → 0 is the last hypothesis of this statement.
By Tendsto.add, ϑ(x)T(r) + E₁(r) + E₂(r) → ϑ(x)∫_P f dHⁿ + 0 + 0 = ϑ(x)∫_P f dHⁿ.

4. Reduction. By Tendsto.congr', it suffices to prove I(r) = ϑ(x)T(r) + E₁(r) + E₂(r) for every r > 0; r > 0 holds eventually in 𝓝[>] 0 by self_mem_nhdsWithin. Fix r > 0 and put G(z) := f(η_r(z)).

5. Integrability. η_r is continuous, so G is continuous. With M a bound for |f| (Continuous.bounded_above_of_compact_support), |G| ≤ M. Hence:
- z ↦ G(z)ϑ(z) is integrable on A (Integrable.bdd_mul: ϑ is integrable on A, and G is a.e.-strongly measurable and bounded by M);
- G is integrable on C, because Hⁿ⌞C is finite (step 2) and G is measurable and bounded (Integrable.of_bound).

6. Change of variables (blowup_cov, r > 0).
- With M := A and θ := ϑ: I(r) = (rⁿ)⁻¹∫_A Gϑ dHⁿ.
- With M := C and θ :≡ 1 (then mul_one): T(r) = (rⁿ)⁻¹∫_C G dHⁿ.

7. Splitting.
- Since C is Borel and Gϑ is integrable on A, ∫_A Gϑ = ∫_{A∩C} Gϑ + ∫_{A∖C} Gϑ (integral_inter_add_sdiff), and A ∩ C = C because C ⊆ A.
- G(z)(ϑ(z) − ϑ(x)) = G(z)ϑ(z) − G(z)ϑ(x). So ∫_C G(ϑ − ϑ(x)) = ∫_C Gϑ − ϑ(x)∫_C G (integral_sub, using integrability of Gϑ on C ⊆ A and of G on C from step 5; integral_mul_const).

8. The identity. Combining steps 6 and 7:
ϑ(x)T(r) + E₁(r) + E₂(r) = (rⁿ)⁻¹[ϑ(x)∫_C G + (∫_C Gϑ − ϑ(x)∫_C G) + ∫_{A∖C} Gϑ]
= (rⁿ)⁻¹[∫_C Gϑ + ∫_{A∖C} Gϑ] = (rⁿ)⁻¹∫_A Gϑ = I(r) (ring arithmetic).

9. Conclusion. By steps 3, 4 and 8, I(r) → ϑ(x)∫_P f dHⁿ as r ↓ 0. As f ∈ C_c was arbitrary, together with step 1 this proves HasWeightedApproximateTangentSpaceAt n A ϑ x P. ∎

## Key steps

1. finrank P = n from T_x C = P
2. three limits: ϑ(x)∫_{η_r(C)} f → ϑ(x)∫_P f by T_x C = P; E₁ → 0 by freeze_weight fed by ball_mass_bound; E₂ → 0 by tail_vanish with S = A ∖ C
3. change of variables (blowup_cov): I(r) = (rⁿ)⁻¹∫_A f(η_r z)ϑ(z) and ∫_{η_r(C)} f = (rⁿ)⁻¹∫_C f(η_r z)
4. split ∫_A = ∫_C + ∫_{A∖C} and isolate ϑ(x): I(r) = ϑ(x)∫_{η_r(C)} f + E₁(r) + E₂(r) for every r > 0
5. Tendsto.congr' gives I(r) → ϑ(x)∫_P f for every f ∈ C_c

## Reference use

### local-project

Queries:
- `cat parent-child-handoff.json, parent-supplied-plan.md and parent-supplied-natural-proof.json of node root-regular-set-open-dense-a1-ae-approx-tangent-exists-a1-weighted-f-298de173be`
- `python3 over dag.json: status, lean_name and lean_statement of all nodes under root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1`
- `python3 over dag.json: nodes whose lean_name or lean_statement mentions blowUp, Lusin, withDensity or continuousOn; duplicate lean_name check; exact string comparison of the selected, rsod_blowUp_setIntegral_eq and rsod_ae_tendsto_density_zero_outside types`
- `grep -n 'def blowUpMap|def HasApproximateTangentSpaceAt|def HasWeightedApproximateTangentSpaceAt' .lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -n 'theorem' .lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `#check of 31 cited library names after `import GMT.Ch05.Submission` (Scratch/LibCheck.lean), including Chapter01.IsBorelRegularOuterMeasure.exists_isClosed_continuousOn, Chapter01.exists_isClosed_continuousOn_of_measurable and Chapter01.closedSetsAreGDelta_iff`
- `grep -rln Lusin <snapshot>/mathlib/Mathlib/MeasureTheory`
- `git show 98fd790d (rsod_blowUp_setIntegral_eq) and 2bf50ebc (aetp_lusin_compact_exhaustion); git branch -a --contains 98fd790d; git merge-base --is-ancestor 98fd790d on every ae-approx-tangent branch; git diff --stat ea560759 4426c5c3/e85cf00b/98fd790d -- GMT/`
- `grep -n '_existing_lean_name_problem|_overlay_accepted_children|_accepted_checkpoint|def _solve_children|def ensure' /runtime/flows/gmt-claude-dce97d36d07f/_recursive_lean/{runtime,store}.py`
- `grep -rl rsod_wfu over the run dir (excluding local-references), GMT, .lake/packages/simongmt, <snapshot>/project and <snapshot>/mathlib/Mathlib; git grep -q rsod_wfu <tip> -- '*.lean' over 402 distinct ref tips`
- `grep -n '1.5 Remark|1.8 Remark|1.17 Theorem' book/chapter-03.txt and book/chapter-01.txt`
- `grep import/prefix/frozen in verifier/gmt-compare.py and verifier/lean_contract.py`
- `cmp GMT/Ch05/{Submission,Contract}.lean against the snapshot project copies; lake-manifest.json revisions`
- `lake build GMT.Ch05.Submission and lake env lean Scratch/{Stmts,Assembly,Pointwise,LibCheck,Tail,Freeze,Mass,Lusin,All2,Challenge2,Solution2}.lean in /tmp/wfu-decomp-Y9uffV`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-ae-approx-tangent-exists-a1-weighted-f-298de173be/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-ae-approx-tangent-exists-a1-weighted-f-298de173be/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-density-of-approx-tangent-a1-blowup-ch-45b63ae1fc/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-density-of-approx-tangent-a1-blowup-ch-45b63ae1fc/accepted-candidate.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-ae-approx-tangent-exists-a1/decomposition-v4.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.lake/packages/simongmt/Poincare/SimonGMT/Chapter01/Lusin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-01.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-dce97d36d07f/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-dce97d36d07f/_recursive_lean/store.py`
- `/tmp/wfu-decomp-Y9uffV/Scratch/LibCheck.lean`
- `/tmp/wfu-decomp-Y9uffV/Scratch/All2.lean`
- `/tmp/wfu-decomp-Y9uffV/Scratch/Challenge2.lean`
- `/tmp/wfu-decomp-Y9uffV/Scratch/Solution2.lean`
- `/tmp/wfu-decomp-Y9uffV/Scratch/final_stmts.json`

Pins and frozen definitions:
- Project ea560759 (workspace HEAD, equal to the manifest project_commit), Mathlib 25730c7c, simongmt 2b366308.
- The workspace Submission.lean and Contract.lean are byte-identical to the snapshot copies.
- The selected node's dispatch base 4426c5c3 adds no Lean declarations.
- Rectifiable.lean confirms the frozen definitions: blowUpMap x r y = r⁻¹ • (y − x), and both approximate-tangent predicates are finrank P = n plus the 𝓝[>] 0 limit for every f : C_c.

Lusin:
- SimonGMT's Chapter01 Lusin theorems (IsBorelRegularOuterMeasure.exists_isClosed_continuousOn, exists_isClosed_continuousOn_of_measurable) and closedSetsAreGDelta_iff are unknown after `import GMT.Ch05.Submission`.
- In snapshot Mathlib/MeasureTheory, 'Lusin' occurs only in Jacobian.lean and Constructions/Polish/Basic.lean (Lusin–Souslin), not as a Lusin continuity theorem.
- So the Lusin child uses Measure.WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure, MeasurableSet.exists_isClosed_sdiff_lt and rational intervals, as accepted commit 2bf50ebc does for aetp_lusin_compact_exhaustion.
- The 31 cited names were checked by #check after `import GMT.Ch05.Submission`: 26 resolve (integral_inter_add_sdiff, norm_integral_le_of_norm_le, Integrable.bdd_mul, withDensity_apply, Measure.restrict_restrict, …). Of the 5 that fail, 4 are the unreachable SimonGMT names above and Lusin's IsCaratheodoryMeasurable-based route that the proofs do not use. The fifth, MeasureTheory.MeasurableEmbedding.integral_map, simply lives in the root namespace as MeasurableEmbedding.integral_map, which the accepted cov proof uses. Every other cited name is exercised by the compiled scratch proofs.

Reuse:
- rsod_blowUp_setIntegral_eq is accepted (node root.regular_set_open_dense-a1.density_of_approx_tangent-a1.blowup_change_of_variables-a1, candidate 98fd790d, which adds only that theorem). Its dag.json type is string-identical to the proposed blowup_cov type.
- The controller (runtime.py _existing_lean_name_problem, _solve_children, _install_parent_supplied_child_handoff, _overlay_accepted_children; store.ensure) shares such accepted nodes across branches.
- The accepted aetp_lusin_compact_exhaustion, tae_mult_lusin_compact_pieces and aetp_weightedTangent_of_lusin_compact require a RectifiableVarifold (countably rectifiable carrier, positive multiplicity), so they do not apply to a general A and real-valued ϑ.

Names: the prefix rsod_wfu occurs nowhere in:
- dag.json or other run files (local-references excluded);
- GMT, simongmt, the snapshot project or snapshot Mathlib;
- .lean files at any of the 402 distinct git ref tips.

Source text: book/chapter-03.txt (Remarks 1.5(3), 1.8(1); Def. 1.7) and book/chapter-01.txt (Thm 1.17) match the children.

Lean (scratch /tmp/wfu-decomp-Y9uffV, v4.35.0-rc3):
- All 7 types elaborate in the frozen Contract scope, and every `exact Submission.X` typechecks.
- The five new children (with the accepted cov proof) have complete proofs whose axioms are only propext, Classical.choice and Quot.sound.
- The selected theorem compiles from them, with sorryAx only from the stubbed dependency rsod_ae_tendsto_density_zero_outside.
- The scratch Submission.lean was restored to pristine afterwards.

No Matrix/IsUnit construction occurs.
