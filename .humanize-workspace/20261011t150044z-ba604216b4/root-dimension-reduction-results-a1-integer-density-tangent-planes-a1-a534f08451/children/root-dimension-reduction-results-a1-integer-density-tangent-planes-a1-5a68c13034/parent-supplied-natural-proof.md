# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.tangent_measures-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.tangent_measures-a1.density_homogeneous-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof step 6 (homogeneous density of the tangent cone weight, (F5)). It is stated here for any measure with the degree-n homogeneity that the sibling cone_measure_homogeneous (Submission.cone_current_imrep_measure_smul_image) provides for the weight of a cone.
Notation: ω_n := unitBallVolume n ∈ [0, ∞]; no finiteness or positivity of ω_n is used. Write h(ρ) := r_ν(w, ρ) = ν(B_ρ(w))/(ω_n·ofReal(ρ^n)).
1. (Scaled balls.) Fix t > 0 and w ∈ ℝ^P, and let ρ > 0. By smul_ball (t ≠ 0), t•B_{ρ/t}(w) = B_{‖t‖·(ρ/t)}(t•w) = B_ρ(t•w), since ‖t‖ = |t| = t and t·(ρ/t) = ρ. Also t•B = (v ↦ t v)''B (Set.image_smul). So B_ρ(t w) = (v ↦ t v)''B_{ρ/t}(w).
2. (Numerator.) Balls are measurable, so the hypothesis with λ := t and A := B_{ρ/t}(w) gives ν(B_ρ(t w)) = ofReal(t^n)·ν(B_{ρ/t}(w)).
3. (Denominator.) ρ^n = (t·(ρ/t))^n = t^n·(ρ/t)^n (mul_pow). Since t^n ≥ 0, ofReal(ρ^n) = ofReal(t^n)·ofReal((ρ/t)^n) (ENNReal.ofReal_mul). Hence ω_n·ofReal(ρ^n) = ofReal(t^n)·(ω_n·ofReal((ρ/t)^n)), using commutativity and associativity in [0, ∞].
4. (Cancellation.) c := ofReal(t^n) satisfies c ≠ 0 (t^n > 0, ENNReal.ofReal_pos) and c ≠ ∞ (ENNReal.ofReal_ne_top). By ENNReal.mul_div_mul_left, r_ν(t w, ρ) = (c·ν(B_{ρ/t}(w)))/(c·(ω_n·ofReal((ρ/t)^n))) = ν(B_{ρ/t}(w))/(ω_n·ofReal((ρ/t)^n)) = h(ρ/t). This holds for every ρ > 0.
5. (Eventual equality.) The set (0, ∞) belongs to 𝓝[>]0 (self_mem_nhdsWithin). So by step 4, ρ ↦ r_ν(t w, ρ) and h ∘ (ρ ↦ ρ/t) agree eventually along 𝓝[>]0 and have the same limsup there (Filter.limsup_congr).
6. (Change of variables.) limsup_{𝓝[>]0} (h ∘ (·/t)) = limsup_{map (·/t) 𝓝[>]0} h (Filter.limsup_comp).
7. (The substitution preserves 𝓝[>]0.) The maps ρ ↦ ρ/t and ρ ↦ tρ are mutually inverse (t ≠ 0). So map (·/t) F = comap (t·) F for every filter F on ℝ (Filter.map_eq_comap_of_inverse). Also comap (t·) 𝓝[>]0 = 𝓝[>]0 because t > 0 (comap_mulLeft_nhdsGT_zero). Hence map (·/t) 𝓝[>]0 = 𝓝[>]0.
8. Combining steps 5–7: limsup_{ρ→0⁺} r_ν(t w, ρ) = limsup_{ρ→0⁺} h(ρ/t) = limsup_{ρ→0⁺} h(ρ) = limsup_{ρ→0⁺} r_ν(w, ρ). ∎

## Key steps

1. B_ρ(tw) = (v ↦ tv)''B_{ρ/t}(w), so ν(B_ρ(tw)) = ofReal(t^n)·ν(B_{ρ/t}(w)), and ω_n·ofReal(ρ^n) = ofReal(t^n)·ω_n·ofReal((ρ/t)^n).
2. Cancelling the finite nonzero factor ofReal(t^n) (ENNReal.mul_div_mul_left) gives r_ν(tw, ρ) = r_ν(w, ρ/t) for every ρ > 0.
3. The limsup along 𝓝[>]0 is unchanged by the substitution ρ ↦ ρ/t: limsup_congr, limsup_comp, and map (·/t) 𝓝[>]0 = comap (t·) 𝓝[>]0 = 𝓝[>]0.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; python3 -I json.load(local-references/123e8435b4a2469b/manifest.json)`
- `python3 scan of dag.json lean_statement fields for 'measure = 0', 'ball (t • w)', 'restrict G', 'HasCompactSupport f → ∀ᶠ', 'boundarySupport T = ∅', '(0 : GeometricCurrentOn', 'IsMinimizingIn (0', 'BoundaryVanishes (0', 'limsup (fun ρ', 'map (dilation' (status and lean_name of each match)`
- `python3 lookup in dag.json of dtc_blowUp_scaling, idtp_tpf_blowUp_limit_boundaryVanishes, dimred_im_mass_measure, cone_current_imrep_measure_smul_image, idtp_fons_cc_ambient_calculus, cmcsd_zero_isIntegerMultiplicity, cmcsd_support_calculus, cbr_cc_current_algebra and the cone_class-a1 children (status, candidate_commit, lean_statement); extraction of subproblem fields from the reused nodes' parent-child-handoff.json and from cone_class decomposition-v1.json`
- `grep -n '^theorem|^def|^instance|^structure' .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/{Currents,CurrentLocalEquality,Mass}.lean; sed -n 95,160p and 275,340p Currents.lean; sed -n 95,140p CurrentLocalEquality.lean; sed -n 50,100p Mass.lean; grep -n countablyRectifiable_of_measure_zero Chapter03/Rectifiable.lean`
- `grep -rn in local-references/123e8435b4a2469b/mathlib/Mathlib: setIntegral_eq_integral_of_forall_compl_eq_zero, restrict_map, restrict_smul, Homeomorph.measurableEmbedding, integral_eq_zero_of_ae, ae_zero, aestronglyMeasurable_zero_measure, tendsto_inv_nhdsGT_zero, Tendsto.const_mul_atTop, comap_mulLeft_nhdsGT_zero, map_eq_comap_of_inverse, limsup_comp, limsup_congr, mul_div_mul_left, smul_ball, image_smul, self_mem_nhdsWithin, tendsto_nhdsWithin_iff, isCompact_closedBall`
- `python3 scan of dag.json lean_name for idtp_fons_cc_tm_* ; git log --all --oneline -S idtp_fons_cc_tm_ (both empty)`
- `sed -n 300,312p, 324,340p, 452,468p /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `runtime.py: _decompose (max_depth gate), _solve_children (existing_by_name reuse), _existing_lean_name_problem, _dependency_problem, _topological, _accepted_checkpoint, _install_parent_supplied_child_handoff, _overlay_accepted_children; store.py ensure`
- `lake env lean /tmp/tm_split_q7/Types.lean, AssemblyAx.lean, N1.lean, N2.lean, N3.lean, N4.lean, Combined.lean (#print axioms); python3 -I /tmp/tm_split_q7/replay.py dag.json`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-a534f08451/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-5982ed9bb9/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-scaling-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-34a94daa02/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Filter.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Order/Field.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/LiminfLimsup.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Basic/ENNReal/Inv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Ball/Pointwise.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Group/Pointwise/Set/Scalar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/AtTopBot/Field.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/NhdsWithin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/store.py`
- `/tmp/tm_split_q7/Types.lean`
- `/tmp/tm_split_q7/AssemblyAx.lean`
- `/tmp/tm_split_q7/N1.lean`
- `/tmp/tm_split_q7/N2.lean`
- `/tmp/tm_split_q7/N3.lean`
- `/tmp/tm_split_q7/N4.lean`
- `/tmp/tm_split_q7/Combined.lean`
- `/tmp/tm_split_q7/replay.py`

Pins match. The manifest's project_commit b4d606db1 equals the workspace HEAD; Mathlib is 25730c7c and SimonGMT 2b366308. The snapshot Contract.lean is byte-identical to the workspace Contract.lean, which equals Submission.lean.

No DAG node, commit or name uses the prefix idtp_fons_cc_tm_. No DAG lean_statement states the zero minimizing cycle with zero weight, the blow-up integral localization or null-ball facts, or the homogeneity of limsup density ratios; 'ball (t • w)' and 'restrict G' occur only in the selected node. The accepted cmcsd_zero_isIntegerMultiplicity and cmcsd_support_calculus give only IsIntegerMultiplicity 0 and spt 0 = ∅ in univ.

Reused at byte-identical types: dtc_blowUp_scaling (accepted, a94d596c) and idtp_tpf_blowUp_limit_boundaryVanishes (accepted, f498a8ef). The sibling idtp_fons_cc_ambient_calculus is still decomposing under cone_class, so it cannot be registered here. Its items (2)–(4) and (9) are reproved inside blowup_integrals; the selected node keeps it as a dependency for Part (B).

Library facts used, SimonGMT:
- Zero instance and zero_apply (Chapter06/Currents.lean:313, 317); GeometricCurrentOn.ext (:305); boundary_apply (:333).
- zeroRegion, support and support_subset_domain (CurrentLocalEquality.lean:108, 115, 125); massOn (Mass.lean:68).
- countablyRectifiable_of_measure_zero (Chapter03/Rectifiable.lean:45).

Library facts used, snapshot Mathlib:
- Measure theory: setIntegral_eq_integral_of_forall_compl_eq_zero (Integral/Bochner/Set.lean:486, no measurability hypothesis); MeasurableEmbedding.restrict_map (Measure/Restrict.lean:890); Measure.restrict_smul (Restrict.lean:193); Homeomorph.measurableEmbedding (BorelSpace/Basic.lean:567); integral_eq_zero_of_ae (Bochner/Basic.lean:349); ae_zero (Measure/Filter.lean:50); aestronglyMeasurable_zero_measure (AEStronglyMeasurable.lean:129).
- Filters and limits: tendsto_inv_nhdsGT_zero (Topology/Algebra/Order/Field.lean:61); comap_mulLeft_nhdsGT_zero (same file, :308); Filter.map_eq_comap_of_inverse (Order/Filter/Map.lean:750); limsup_comp and limsup_congr (Order/LiminfLimsup.lean:90, 201); Tendsto.const_mul_atTop (AtTopBot/Field.lean:72).
- Arithmetic and geometry: ENNReal.mul_div_mul_left (Basic/ENNReal/Inv.lean:264); smul_ball (Normed/Module/Ball/Pointwise.lean:79); Set.image_smul (Pointwise/Set/Scalar.lean:155).

Lean results: all child types elaborate. zero_cycle, blowup_integrals and density_homogeneous are fully proved using only the standard axioms. support_blowup is proved from DTC and the two reused frozen types. The selected type is proved from the four new children and its registered dependencies dimred_im_mass_measure, cone_current_imrep_measure_smul_image and idtp_fons_cc_ambient_calculus. The runtime replay accepts the split.
