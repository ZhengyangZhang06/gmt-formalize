# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.arc_continuation-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.two_dim_cone_density-a1.arc_continuation-a1.endpoint_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 3 and 4 of the parent proof, with the first-failure parameter φ* renamed φ₀ and only the arc hypothesis on (0, φ₀) retained. Notation: γ(φ) := cos φ·z + sin φ·e, a := γ(φ₀), e_a := sin φ₀·z − cos φ₀·e, B_r(x) the open ball. For 0 < φ < φ₀ let ε_φ > 0 be given by the hypothesis: spt C ∩ B_{ε_φ}(γ(φ)) = Q ∩ B_{ε_φ}(γ(φ)), and HasMassDensity C y k for every y ∈ spt C ∩ B_{ε_φ}(γ(φ)).
0. Facts. (a) By the sibling Submission.idtp_tdc_acont_great_circle (applied to z, e): |γ(φ)| = 1 and |γ(φ) − γ(ψ)| ≤ |φ − ψ| for all φ, ψ; |e_a| = 1; ⟨a, e_a⟩ = 0; and cos ψ·a + sin ψ·e_a = γ(φ₀ − ψ) for every ψ. (b) Q is a linear subspace containing z and e, so γ(φ) ∈ Q for every φ, in particular a ∈ Q, and e_a ∈ Q. (c) C is integer multiplicity (the first component of IsMinimizingIn C univ). Hence for each t > 0 the frozen prerequisite Submission.idtp_tdc_cone_dilation (with n := 2 and s := t) gives: t·x ∈ spt C ⟺ x ∈ spt C for every x, and HasMassDensity C (t·x) θ ⟺ HasMassDensity C x θ for all x and θ. (d) spt C is closed: by definition C.support = univ ∖ C.zeroRegion, and the zero region is open (GeometricCurrentOn.isOpen_zeroRegion).
1. (Arc points.) Let 0 < φ < φ₀. Since γ(φ) ∈ Q (fact (b)) and γ(φ) ∈ B_{ε_φ}(γ(φ)), we get γ(φ) ∈ Q ∩ B_{ε_φ}(γ(φ)) = spt C ∩ B_{ε_φ}(γ(φ)). So γ(φ) ∈ spt C, and then HasMassDensity C γ(φ) k by the density part of the hypothesis with y := γ(φ).
2. (a ∈ spt C.) Let r > 0 and η := min(φ₀, r)/2. Then 0 < η < φ₀ and η < r, so φ₀ − η ∈ (0, φ₀) and γ(φ₀ − η) ∈ spt C by step 1. By fact (a), |a − γ(φ₀ − η)| ≤ |φ₀ − (φ₀ − η)| = η < r. Hence every open ball about a meets spt C, i.e. a ∈ closure(spt C) (Metric.mem_closure_iff), and a ∈ spt C because spt C is closed (fact (d)).
3. (The backward sector satisfies the sector hypothesis.) Let t > 0 and 0 < ψ < φ₀. Put φ := φ₀ − ψ, so 0 < φ < φ₀, and w := γ(φ) = cos ψ·a + sin ψ·e_a (fact (a)). (i) By step 1, HasMassDensity C w k; by fact (c), HasMassDensity C (t·w) k. (ii) Let r := t·ε_φ > 0 and x ∈ spt C ∩ B_r(t·w). Since t·(t⁻¹x) = x ∈ spt C, fact (c) gives t⁻¹x ∈ spt C. Moreover |t⁻¹x − w| = |t⁻¹·(x − t·w)| = t⁻¹|x − t·w| < t⁻¹·t·ε_φ = ε_φ. Hence t⁻¹x ∈ spt C ∩ B_{ε_φ}(w) = Q ∩ B_{ε_φ}(w), so t⁻¹x ∈ Q and x = t·(t⁻¹x) ∈ Q. Thus spt C ∩ B_r(t·(cos ψ·a + sin ψ·e_a)) ⊆ Q.
4. (Sector lemma.) Apply the frozen prerequisite Submission.idtp_cone_sector_endpoint_density with P, C, Q, a, e := e_a, δ := φ₀ and k. Its hypotheses hold: C is minimizing in ℝ^P, ∂C = 0 and C is a cone (given); finrank Q = 2 (given); a, e_a ∈ Q (fact (b)); |a| = 1, |e_a| = 1 and ⟨a, e_a⟩ = 0 (fact (a)); 0 < φ₀ and 1 ≤ k (given); a ∈ spt C (step 2); and for all t > 0 and ψ with 0 < ψ < φ₀, HasMassDensity C (t·(cos ψ·a + sin ψ·e_a)) k together with r > 0 such that spt C ∩ B_r(t·(cos ψ·a + sin ψ·e_a)) ⊆ Q (step 3). It yields HasMassDensity C a k.
5. Steps 2 and 4 give γ(φ₀) = a ∈ spt C and HasMassDensity C γ(φ₀) k. ∎

## Key steps

1. Centres of the Good balls on the arc γ((0, φ₀)) lie in spt C and have density k.
2. a := γ(φ₀) is a limit of arc points (γ is 1-Lipschitz) and spt C is closed, so a ∈ spt C.
3. With e_a := sin φ₀·z − cos φ₀·e, cos ψ·a + sin ψ·e_a = γ(φ₀ − ψ); cone dilation (idtp_tdc_cone_dilation) transfers density k and the local inclusion spt C ⊆ Q to every t·γ(φ₀ − ψ), t > 0.
4. The frozen sector lemma idtp_cone_sector_endpoint_density (δ := φ₀) gives HasMassDensity C a k.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD (compared with manifest.json)`
- `grep -rn 'zeroRegion|def support|isClosed_support|mem_support' .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/*.lean; sed -n 95,145p Chapter06/CurrentLocalEquality.lean`
- `rg -n '(theorem|lemma) (Real\.)?(one_sub_sq_div_two_le_cos|eq_of_le_of_finrank_eq|finrank_span_eq_card|sin_pos_of_pos_of_lt_pi|two_le_pi|Orthonormal.linearIndependent|orthonormal_iff_ite|norm_add_sq_real|real_inner_self_eq_norm_sq|cos_sq_add_sin_sq|cos_sub|sin_sub)\b' mathlib/Mathlib`
- `rg -n -i 'real induction|continuous induction' mathlib/Mathlib; rg -n 'IsClosed.Icc_subset_of_forall_mem_nhdsWithin|IsClosed.mem_of_ge_of_forall_exists_gt|IsClosed.Icc_subset_of_forall_exists_gt' mathlib/Mathlib`
- `rg -n 'theorem mem_closure_iff' mathlib/Mathlib (Metric version in Topology/MetricSpace/Pseudo/Defs.lean)`
- `grep -rn 'theorem pi_gt_three' .lake/packages/mathlib/Mathlib/Analysis/Real/Pi/Bounds.lean (not in the import closure of GMT.Ch07.Submission; Real.two_le_pi used instead)`
- `python3 scan of dag.json: frozen types and statuses of idtp_tdc_arc_continuation, idtp_tdc_cone_dilation, idtp_cone_sector_endpoint_density, idtp_cone_constant_density_planar, dimred_cs_mi_hasMassDensity_unique; lean_name collisions for idtp_tdc_acont_*; exact-type matches for the four child statements; depth>=4 nodes citing non-sibling Submission declarations`
- `regex scan of lean_name fields in nodes/*/decomposition-*.json for acont|idtp_tdc|great_circle|real_induction`
- `git log --all --oneline -S dimred_cs_mi_hasMassDensity_unique; git show a243c0535`
- `lake env lean /tmp/acont-split-a1/gen/{Probe,Child_real_induction,Child_great_circle,Child_endpoint_density,Child_endpoint_plane,Assembly,PureChecks,GmtChecks}.lean`
- `independent reviewer: lake env lean /tmp/acont-review-indep/{Elab,ExactNames,Assembly,AssemblyNoUniq,Pure,Gmt}.lean; python3 /tmp/acont-review-indep/names_check.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Complex/Trigonometric.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Dimension/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/IntermediateValue.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/mathlib/Mathlib/Analysis/Real/Pi/Bounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-d1c42280a2/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-edecc539dd/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-edecc539dd/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-ca9016021f/parent-supplied-natural-proof.md`
- `/tmp/acont-split-a1/gen/Probe.lean`
- `/tmp/acont-split-a1/gen/Child_real_induction.lean`
- `/tmp/acont-split-a1/gen/Child_great_circle.lean`
- `/tmp/acont-split-a1/gen/Child_endpoint_density.lean`
- `/tmp/acont-split-a1/gen/Child_endpoint_plane.lean`
- `/tmp/acont-split-a1/gen/Assembly.lean`
- `/tmp/acont-split-a1/gen/PureChecks.lean`
- `/tmp/acont-split-a1/gen/GmtChecks.lean`
- `/tmp/acont-review-indep/Elab.lean`
- `/tmp/acont-review-indep/ExactNames.lean`
- `/tmp/acont-review-indep/Assembly.lean`
- `/tmp/acont-review-indep/AssemblyNoUniq.lean`
- `/tmp/acont-review-indep/Pure.lean`
- `/tmp/acont-review-indep/Gmt.lean`

Pins and contract:
- The workspace HEAD b4d606db, mathlib 25730c7c and SimonGMT 2b366308 match manifest.json.
- The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

SimonGMT:
- GeometricCurrentOn.support = U \ zeroRegion, and GeometricCurrentOn.isOpen_zeroRegion holds (CurrentLocalEquality.lean lines 108–124). So spt C is closed when U = univ; endpoint_density uses this.

Mathlib snapshot: it contains every lemma the child proofs cite.
- Real.one_sub_sq_div_two_le_cos (Trigonometric/Bounds.lean:124).
- Real.cos_sub, Real.sin_sub and cos_sq_add_sin_sq (Complex/Trigonometric.lean).
- real_inner_self_eq_norm_sq and norm_add_sq_real (InnerProductSpace/Basic.lean).
- Orthonormal.linearIndependent and orthonormal_iff_ite (InnerProductSpace/Orthonormal.lean).
- finrank_span_eq_card (Dimension/Constructions.lean:463).
- Submodule.eq_of_le_of_finrank_eq (FiniteDimensional/Basic.lean:257).
- Real.sin_pos_of_pos_of_lt_pi and Real.two_le_pi (Trigonometric/Basic.lean).
- Metric.mem_closure_iff (MetricSpace/Pseudo/Defs.lean:1220).
Negative findings:
- Mathlib's continuous-induction principles (IsClosed.Icc_subset_of_forall_mem_nhdsWithin and IsClosed.mem_of_ge_of_forall_exists_gt in Topology/Order/IntermediateValue.lean) require s ∩ [a, b] to be closed, which does not match real_induction's left-step hypothesis. That child is therefore proved directly by an sInf argument.
- Real.pi_gt_three lies outside the import closure, so Real.two_le_pi is used instead.

DAG:
- These frozen types were read from dag.json and used verbatim in the Lean checks: idtp_tdc_arc_continuation (equal to the handoff), idtp_tdc_cone_dilation, idtp_cone_sector_endpoint_density, idtp_cone_constant_density_planar, and the accepted dimred_cs_mi_hasMassDensity_unique (commit a243c0535; integrated_commit empty, so an inline fallback is recorded).
- No DAG declaration has any proposed child type, so there is nothing to reuse.
- The four idtp_tdc_acont_* names are unreserved in dag.json and in every decomposition file.

Lean checks:
- All four child statements elaborate.
- These compile with axioms propext, Classical.choice and Quot.sound only:
  - the hypothesis-only assembly of the exact parent type, both with the uniqueness lemma and with uniqueness proved inline;
  - complete proofs of real_induction and great_circle;
  - proofs of endpoint_density and endpoint_plane from great_circle plus the frozen black-box types.
- The independent reviewer reproduced all of these from the exact strings.
