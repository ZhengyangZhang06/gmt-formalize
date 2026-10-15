# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_splitting-a1.subspace_projection-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_splitting-a1.subspace_projection-a1.projected_mass-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 4 of the selected node's supplied proof (projection does not increase mass: |Λ_m q ξ_S(x)| ≤ Π|qτ_i| ≤ 1 by Hadamard's inequality, hence M_{W*}(q_#S) ≤ μ_S(q^{−1}(W*))), together with q_#T = T from its step 1. Here S' = T + q_#X plays the role of q_#S = q_#T + q_#X, and the representation R of T + X (= S) is built so that its action is additive on the non-compactly supported forms q^#ω.
Siblings used: int_combination (Submission.rsdic_exists_imrep_int_combination), projection_invariance (Submission.idtp_fons_cs_sp_action_starProjection_eq), orient_comp (Submission.dtc_bc_lc_pf_unitOrientation_comp) and pairing_bound (Submission.dpf_pfc_imrep_pairing_integrable_abs_le).
Notation: μ := H^m = μHE[m]. For an IMRep R write M_R, θ_R, ξ_R for carrier, mult and orient, and F_R(x) := 1_{M_R}(x)·θ_R(x)·ξ_R(x) ∈ Λ_m(ℝ^P) (R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y)). ‖·‖ is the operator norm of a covector or a linear map, |·|_E the Euclidean coefficient norm (covectorEuclideanNorm). q is an orthogonal projection, so ‖q‖ ≤ 1 (starProjection_norm_le); V is closed.
1. Action as a global integral. For every IMRep R and every m-form β, F_R(x)(β(x)) = 1_{M_R}(x)·θ_R(x)·ξ_R(x)(β(x)), so R.action(β) = ∫_{M_R} θ_R ξ_R(β) dμ = ∫ F_R(x)(β(x)) dμ(x) (integral_indicator, M_R measurable). If x ↦ θ_R ξ_R(β) is μ⌞M_R-integrable, then x ↦ F_R(x)(β(x)) is μ-integrable (integrable_indicator_iff).
2. Carriers. If C is measurable and R.measure(Cᶜ) = 0, then μ⌞M_R-a.e. x lies in C. Indeed 0 = R.measure(Cᶜ) = ∫⁻_{M_R ∩ Cᶜ} θ_R dμ (withDensity_apply, restrict_restrict) ≥ μ(M_R ∩ Cᶜ) because θ_R ≥ 1 on M_R; conclude with ae_restrict_iff'.
3. Projected orientation bound. For every IMRep R, for μ⌞M_R-a.e. x and every m-covector α: |ξ_R(x)(α∘Λ^m q)| ≤ |α|_E. Proof: by the field orients, for μ⌞M_R-a.e. x there is a subspace Q with IsUnitOrientationOf (ξ_R x) Q, i.e. ξ_R(x) = ±τ_1∧⋯∧τ_m for an orthonormal basis τ of Q. The first part of orient_comp with L := q gives |ξ_R(x)(α∘Λ^m q)| ≤ |α|_E·‖q‖^m (in Simon's terms |⟨α, Λ_m q ξ⟩| = |α(qτ_1, …, qτ_m)| ≤ |α|_E·Π_i|qτ_i|, Hadamard's inequality). Since ‖q‖ ≤ 1 and |α|_E ≥ 0 (covectorEuclideanNorm_nonneg), ‖q‖^m ≤ 1 (pow_le_one₀) and |ξ_R(x)(α∘Λ^m q)| ≤ |α|_E.
4. The combined triple. Apply int_combination with U = ℝ^P (open), R₁ = RT, R₂ = RX and p₁ = p₂ = 1. It gives an IMRep R with F_R = F_RT + F_RX μ-a.e.
5. Additivity. Let β be an m-form such that x ↦ θ_RT ξ_RT(β) is μ⌞M_RT-integrable and x ↦ θ_RX ξ_RX(β) is μ⌞M_RX-integrable. By steps 1 and 4, R.action(β) = ∫ F_R(β) dμ = ∫ (F_RT + F_RX)(β) dμ (integral_congr_ae) = ∫ F_RT(β) dμ + ∫ F_RX(β) dμ (integral_add, integrability from step 1) = RT.action(β) + RX.action(β).
6. Test forms; the first conclusion. Let ω be a test form. It is continuous (hence a.e. strongly measurable for every measure) with compact support C := tsupport ω, hence bounded by some B (Continuous.bounded_above_of_compact_support), and ω(x) = 0 off C (image_eq_zero_of_notMem_tsupport). So pairing_bound (with U = ℝ^P, F := ω) shows that θ_R ξ_R(ω) is μ⌞M_R-integrable for every IMRep R in ℝ^P. Step 5 gives R.action(ω) = RT.action(ω) + RX.action(ω) = T(ω) + X(ω), since RT represents T and RX represents X.
7. Pull-backs of test forms. Fix a test form ω, let B bound ‖ω‖ and put β := q^#ω, β(x) = ω(0 + q x)∘Λ^m q. Then β is continuous (composition of ω, x ↦ q x and the continuous linear map α ↦ α∘Λ^m q) and ‖β(x)‖ ≤ ‖ω(q x)‖·‖q‖^m ≤ B (ContinuousAlternatingMap.norm_compContinuousLinearMap_le, ‖q‖ ≤ 1).
 General principle: let R be an IMRep, D a closed set, C a compact set with R.measure(Dᶜ) = 0 and β(x) = 0 for x ∈ D ∖ C. Then θ_R ξ_R(β) is μ⌞M_R-integrable. Indeed F := 1_D·β is a.e. strongly measurable (β is continuous and D is Borel), vanishes off C (on D ∖ C because β does, and off D by definition), and ‖F(x)‖ ≤ B for all x (B ≥ ‖β(x)‖ ≥ 0, which also covers x ∉ D where F(x) = 0), so pairing_bound gives integrability of θ_R ξ_R(F). By step 2, F = β μ⌞M_R-a.e., so θ_R ξ_R(β) is integrable (Integrable.congr).
 (a) For RX take D = C = K (compact, hence closed); the vanishing condition is empty.
 (b) For RT take D = V and C = V ∩ tsupport ω (compact). If x ∈ V ∖ tsupport ω, then q x = x and ω(q x) = ω(x) = 0, so β(x) = 0.
 Hence step 5 applies to β, and with projection_invariance (applicable because RT.measure(Vᶜ) = 0) R.action(q^#ω) = RT.action(q^#ω) + RX.action(q^#ω) = RT.action(ω) + RX.action(q^#ω) = T(ω) + RX.action(q^#ω) = S'(ω).
8. Mass bound; the second conclusion. Fix O ⊆ ℝ^P. Let ω be admissible for S'.massOn O, i.e. tsupport ω ⊆ O and |ω(y)|_E ≤ 1 for all y, and let β = q^#ω. By step 7, ofReal(S'(ω)) = ofReal(R.action β) ≤ ofReal(|R.action β|) ≤ ∫⁻_{M_R} |θ_R(x)·ξ_R(x)(β(x))| dμ (enorm_integral_le_lintegral_enorm). For μ⌞M_R-a.e. x (step 3):
 - if q x ∈ tsupport ω, then |ξ_R(x)(β(x))| = |ξ_R(x)(ω(q x)∘Λ^m q)| ≤ |ω(q x)|_E ≤ 1;
 - if q x ∉ tsupport ω, then ω(q x) = 0, so β(x) = 0.
 So the integrand is at most θ_R(x)·1_{q⁻¹(tsupport ω)}(x), and ∫⁻_{M_R} θ_R 1_{q⁻¹(tsupport ω)} dμ = R.measure(q⁻¹(tsupport ω)) (lintegral_indicator and withDensity_apply; q⁻¹(tsupport ω) is closed, hence measurable) ≤ R.measure(q⁻¹(O)), since tsupport ω ⊆ O. As S'.massOn O is the supremum of ofReal(S'(ω)) over admissible ω (sSup_le), S'.massOn O ≤ R.measure(q⁻¹(O)). ∎
Formalization note: this proof was compiled after import GMT.Ch07.Submission, with the statements of the four siblings as hypotheses; #print axioms reports only propext, Classical.choice and Quot.sound.

## Key steps

1. Unit orientations ξ = ±τ₁∧⋯∧τ_m satisfy |ξ(α∘Λ^m q)| ≤ |α|_E·‖q‖^m ≤ |α|_E (orient_comp, ‖q‖ ≤ 1).
2. int_combination gives R with vector density F_R = F_RT + F_RX a.e., so R.action is additive on forms whose pairings with RT and RX are integrable.
3. Test forms and the pull-backs q^#ω are integrable against RT and RX (pairing_bound; RT lives on V where q^#ω vanishes off tsupport ω, RX lives on the compact K). Hence R represents T + X and, by projection_invariance, R.action(q^#ω) = S'(ω).
4. For admissible ω with tsupport ω ⊆ O, |S'(ω)| ≤ ∫_{M_R} θ_R 1_{q⁻¹(tsupport ω)} dH^m = μ_R(q⁻¹(tsupport ω)) ≤ μ_R(q⁻¹(O)).

## Reference use

### local-project

Queries:
- `python3 -I json.load(<snapshot>/manifest.json); git rev-parse HEAD (b4d606db1da5…, equal to manifest project_commit); git -C .lake/packages/mathlib rev-parse HEAD (25730c7c…, equal to manifest mathlib_commit); git -C .lake/packages/simongmt rev-parse HEAD (2b366308…)`
- `cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; cmp GMT/Ch07/Contract.lean <snapshot>/project/GMT/Ch07/Contract.lean (both identical)`
- `rg -n '^def IsMinimizingIn|^def SameBoundary|^def CompactlyContained|^structure IMRep|IMRep.measure|IMRep.action|^def IsIntegerMultiplicity|^def ' <snapshot>/project/GMT/Ch07/Contract.lean; sed -n 1,145p of the same file`
- `rg -n 'theorem (starProjection_norm_le|starProjection_eq_self_iff|norm_starProjection_apply_le)' <snapshot>/mathlib/Mathlib/Analysis/InnerProductSpace/Projection`
- `rg -n '(theorem|lemma) (measure_compl_support|measure_inter_conull)' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure/{Support,Basic}.lean`
- `rg -n 'theorem ext_of_generateFrom_of_iUnion' <snapshot>/mathlib/Mathlib/MeasureTheory/Measure; rg -n 'theorem enorm_integral_le_lintegral_enorm' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral; rg -n 'theorem norm_compContinuousLinearMap_le' <snapshot>/mathlib/Mathlib/Analysis/Normed; rg -n 'theorem isPiSystem_isOpen' <snapshot>/mathlib/Mathlib/MeasureTheory`
- `rg -l 'GeometricCurrentOn|IntegerMultiplicity' <snapshot>/mathlib/Mathlib/{MeasureTheory,Geometry,Analysis} (no match: Mathlib has no currents or push-forward of integer multiplicity currents)`
- `rg -n 'idtp_fons_cs_sp_|dtc_bc_lc_pushforward|dor_imrep_massOn_eq_measure_and_support|atsm_approxTangent_le_of_flat' <snapshot>/project (no match); rg -n 'idtp_fons_cs_sp_' GMT .lake/packages/simongmt (no match)`
- `grep -n 'def affinePullbackForm|def massAdmissibleOn' .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/{AffineCurrentPushforward,Mass}.lean`
- `python3 -I scans of dag.json (updated 2026-10-14T08:40:41Z and re-run at 09:16:54Z): for each of the 11 child names, all nodes with that lean_name, their status, candidate_commit, parent and byte equality of lean_statement; replay of Runtime._existing_lean_name_problem, _dependency_problem and _topological; transitive children/depends_on reachability from each reused node to this node's ancestors (none)`
- `git show <candidate_commit>:GMT/Ch07/Submission.lean for b1757de5, d49dda91, 77fcc7d4, 44ef61f7, 0af9ed59, a0bc3cde, 5c8c6597, 038573e4: the declaration `theorem Submission.<name> :` exists once and its type is byte-identical to the child lean_statement`
- `python3 -I comparison of each reused child with the accepted node's parent-child-handoff.json (lean_statement, statement, proof_key_steps, natural_proof)`
- `grep -n '_existing_lean_name_problem|_accepted_checkpoint|def refresh|def update|def ensure|_install_parent_supplied_child_handoff|_solve_children|decomposition_attempts' /runtime/flows/gmt-claude-d253855dab51/{_recursive_lean/runtime.py,_recursive_lean/store.py,__init__.py}; issue-workers.json record of this node (started_at 2026-10-14T00:25:00Z)`
- `git log --all --oneline -S'idtp_fons_cs_sp_' -- GMT/Ch07/Submission.lean (no match); grep -l idtp_fons_cs_sp_ ../.swarm-worktrees/*/gmt-ch07/GMT/Ch07/Submission*.lean (744 worktrees, no match)`
- `sed -n 350,372p book/chapter-07.txt (Simon 7.3.1 footnote 2: orthogonal projection onto T_xN does not increase area)`
- `lake env lean /tmp/sp7_decomp/gen/{Types,AssemblyGen,ProjInvGen,MeasLocGen,ProjMassGen}.lean (Lean v4.35.0-rc3; #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/issue-workers.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-5df916c2fb/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-5df916c2fb/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-a685b45291/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-im-sub-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-vanish-off-support-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-integer-combination-a1-combination-construction-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-9f4d277b67/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-diffeo-pushforward-a1-pushforwa-49ef3e5978/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-approx-tangent-in-submanifold-a-33314200d5/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/store.py`
- `/runtime/flows/gmt-claude-d253855dab51/_recursive_lean/models.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/sp7_decomp/gen/Types.lean`
- `/tmp/sp7_decomp/gen/AssemblyGen.lean`
- `/tmp/sp7_decomp/gen/ProjInvGen.lean`
- `/tmp/sp7_decomp/gen/MeasLocGen.lean`
- `/tmp/sp7_decomp/gen/ProjMassGen.lean`

The pins match. The snapshot manifest records project b4d606db1 (the workspace HEAD) and Mathlib 25730c7c (the workspace Mathlib); SimonGMT is 2b366308. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean, which contain no Submission declarations, so none of the 11 child names occurs in the snapshot.
The snapshot Mathlib has no currents (no GeometricCurrentOn or integer multiplicity match), so the integer multiplicity push-forward by the non-proper projection q is not a library fact. It enters only through the accepted Submission.dtc_bc_lc_pushforward.
The Mathlib facts used by the three new leaves and the parent assembly exist at the pinned revision:
- starProjection_norm_le (Projection/Basic.lean:386), starProjection_eq_self_iff (:290) and norm_starProjection_apply_le (:411);
- measure_compl_support (Measure/Support.lean:202) and measure_inter_conull (Measure/Basic.lean:308);
- ext_of_generateFrom_of_iUnion (Measure/Restrict.lean:491) and isPiSystem_isOpen (BorelSpace/Basic.lean:81);
- enorm_integral_le_lintegral_enorm (Bochner/Basic.lean:333);
- ContinuousAlternatingMap.norm_compContinuousLinearMap_le (Alternating/Basic.lean:432).
In dag.json all 8 reused declarations are accepted with candidate commits and byte-identical types:
- dtc_bc_lc_pushforward b1757de5;
- dor_imrep_massOn_eq_measure_and_support d49dda91;
- dtc_isIntegerMultiplicity_sub 77fcc7d4;
- dtc_vanish_off_support 44ef61f7;
- rsdic_exists_imrep_int_combination 0af9ed59;
- dtc_bc_lc_pf_unitOrientation_comp a0bc3cde;
- dpf_pfc_imrep_pairing_integrable_abs_le 5c8c6597;
- atsm_approxTangent_le_of_flat 038573e4.
Each candidate commit declares exactly that type, and all prerequisites of these nodes are accepted. dtc_bc_lc_pushforward, which was rejected in attempt 1, became accepted only after this node's worker had refreshed its store at 00:25Z. It is now an accepted checkpoint, so Runtime._existing_lean_name_problem allows sharing it at the identical type. The three new idtp_fons_cs_sp_* names occur in no DAG node, git history of Submission.lean, GMT/, SimonGMT, the snapshot or any swarm worktree Submission.lean.
The following were re-run in this attempt:
- all 11 child types and the parent type elaborate;
- the parent assembly compiles from its six child statements;
- the three new leaves compile from their sibling statements;
- #print axioms shows only propext, Classical.choice and Quot.sound.
The runtime gate replay reports no problem.
