# Parent-supplied natural-language proof

- Parent DAG node: `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.weighted_from_unweighted-a1`
- Child DAG node: `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1.weighted_from_unweighted-a1.ball_mass_bound-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 6 of the parent proof (Simon Ch. 3, Remark 1.5(3): a cutoff equal to 1 on a ball, used in Definition 1.4, bounds the density ratio). It is transported to the original side of the blow-up with the sibling blowup_cov (Submission.rsod_blowUp_setIntegral_eq).

Notation: Hⁿ := μHE[n]; η_r := blowUpMap x r, so η_r(z) = r⁻¹(z − x); B_ρ(p) := closedBall p ρ; μ.real S := (μ S).toReal. C is an arbitrary set with Hⁿ(C) < ∞; no measurability of C is used.

1. Cutoff. Fix R > 0 and let g(y) := max(0, min(1, R + 1 − ‖y‖)).
- g is continuous and 0 ≤ g ≤ 1.
- If ‖y‖ ≤ R, then R + 1 − ‖y‖ ≥ 1, so g(y) = 1.
- If ‖y‖ > R + 1, then R + 1 − ‖y‖ < 0, so g(y) = 0.
Thus g vanishes off the compact ball B_{R+1}(0) (isCompact_closedBall). So g has compact support (HasCompactSupport.intro) and defines G ∈ C_c(ℝ^{n+ℓ}, ℝ) with G = g pointwise.

2. Limit. Apply the second conjunct of HasApproximateTangentSpaceAt n C x P to G: ∫_{η_r(C)} g dHⁿ → L := ∫_P g dHⁿ as r → 0 in 𝓝[>] 0. Since L < L + 1, eventually in 𝓝[>] 0 we have ∫_{η_r(C)} g dHⁿ < L + 1 (Tendsto.eventually with gt_mem_nhds). Put Λ := L + 1. Also r > 0 eventually in 𝓝[>] 0 (self_mem_nhdsWithin). Fix r with both properties; it remains to show (rⁿ)⁻¹·Hⁿ.real(C ∩ B_{rR}(x)) ≤ Λ.

3. Change of variables. Apply blowup_cov with M := C, f := g, θ :≡ 1 and r > 0, and simplify the factor 1 (mul_one): ∫_{η_r(C)} g dHⁿ = (rⁿ)⁻¹·∫_C g(η_r(z)) dHⁿ(z).

4. Comparison. Let B := B_{rR}(x), a Borel set.
(a) Pointwise: 1_B(z) ≤ g(η_r(z)) for every z ∈ ℝ^{n+ℓ}.
- If z ∈ B, then ‖z − x‖ ≤ rR, so ‖η_r(z)‖ = r⁻¹‖z − x‖ ≤ r⁻¹·rR = R (norm_smul, r > 0), and g(η_r(z)) = 1 by step 1.
- If z ∉ B, then 1_B(z) = 0 ≤ g(η_r(z)).
(b) Integrability. The measure Hⁿ⌞C is finite because Hⁿ(C) < ∞ (isFiniteMeasure_restrict). Hence two functions are Hⁿ⌞C-integrable:
- 1_B, the indicator of a Borel set with value 1;
- g∘η_r, which is continuous (η_r is continuous) and bounded by 1 (Integrable.of_bound).
(c) By monotonicity of the integral (integral_mono), ∫_C 1_B dHⁿ ≤ ∫_C g∘η_r dHⁿ.
(d) Moreover ∫_C 1_B dHⁿ = (Hⁿ⌞C).real(B) = Hⁿ.real(B ∩ C) = Hⁿ.real(C ∩ B) (integral_indicator_one; Measure.restrict_apply, which needs only B to be Borel).

5. Conclusion. Since (rⁿ)⁻¹ > 0, steps 4, 3 and 2 give (rⁿ)⁻¹·Hⁿ.real(C ∩ B_{rR}(x)) ≤ (rⁿ)⁻¹·∫_C g∘η_r dHⁿ = ∫_{η_r(C)} g dHⁿ < L + 1 = Λ. This holds for all r in a set belonging to 𝓝[>] 0, which is the claim. ∎

## Key steps

1. build the cutoff g = max(0, min(1, R+1−‖y‖)) ∈ C_c with 0 ≤ g ≤ 1 and g = 1 on B_R(0)
2. T_x C = P gives ∫_{η_r(C)} g → ∫_P g, so eventually ∫_{η_r(C)} g < Λ := ∫_P g + 1
3. change of variables (blowup_cov with θ ≡ 1): ∫_{η_r(C)} g = (rⁿ)⁻¹ ∫_C g∘η_r
4. 1_{B_{rR}(x)} ≤ g∘η_r and finiteness of Hⁿ⌞C give Hⁿ(C ∩ B_{rR}(x)) ≤ ∫_C g∘η_r

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
