# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.ray_constancy-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.ray_constancy-a1.boundary_ray_test-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent step 1 ('Testing ∂C = 0'). This is Simon Ch. 6 (6.2.3), ∂T(φ) = T(dφ), applied to the 0-form of f. Lean ingredients: ContinuousAlternatingMap.constOfIsEmpty / constOfIsEmptyLIE, extDeriv_constOfIsEmpty and GeometricCurrentOn.boundary_apply.
Notation: for a 1-covector α and v ∈ ℝ^P, α[v] := α(fun _ => v). C^∞ means ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞). G_e := G(e).
Let P, C, F, G be as in the statement. So C.boundary = 0 and
 (R) C(ω) = Σ_{e∈F} ∫_{(0,∞)} G_e(t)·ω(te)[e] dt for every ω ∈ TestFormOn univ 1.
Let f : ℝ^P → ℝ be C^∞ with compact support.
1. (The test 0-form f̂.) Let L := constOfIsEmptyLIE : ℝ → Covector(ℝ^P, 0), c ↦ constOfIsEmpty(c), the alternating map of no arguments with constant value c. L is a linear isometric equivalence, hence a continuous linear map with L(0) = 0. Put f̂ := L ∘ f, i.e. f̂(x) = constOfIsEmpty(f(x)). Then:
 - f̂ is C^∞, as a continuous linear map composed with the C^∞ map f;
 - f̂ has compact support, by HasCompactSupport.comp_left since L(0) = 0 and f has compact support;
 - tsupport f̂ ⊆ univ trivially.
 Hence f̂ ∈ TestFormOn univ 0.
2. (Its exterior derivative.) exteriorDerivativeTestOn univ 0 f̂ is the test 1-form x ↦ extDeriv f̂ x. By extDeriv_constOfIsEmpty, extDeriv f̂ x = ContinuousAlternatingMap.ofSubsingleton (0 : Fin 1) (Df(x)). Its value on the constant family (fun _ => v) is Df(x)v. Hence (d f̂)(x)[v] = Df(x)v for all x, v ∈ ℝ^P.
3. (Using ∂C = 0.) Since C.boundary = 0 and the zero current vanishes on every test form, 0 = (C.boundary)(f̂). By GeometricCurrentOn.boundary_apply, (C.boundary)(f̂) = C(exteriorDerivativeTestOn univ 0 f̂) = C(d f̂). Apply (R) to ω := d f̂ and rewrite each integrand with step 2 (at x = te, v = e):
 (3.1) Σ_{e∈F} ∫_{(0,∞)} G_e(t)·Df(te)e dt = 0.
4. (Chain rule.) f is C^∞, hence differentiable at every point. Fix e ∈ ℝ^P and t ∈ ℝ. The map s ↦ s·e has derivative 1·e = e at t (the identity has derivative 1, then HasDerivAt.smul_const), and f has Fréchet derivative Df(te) at te. By the chain rule (HasFDerivAt.comp_hasDerivAt), s ↦ f(s·e) has derivative Df(te)e at t. Hence deriv (fun s => f(s•e)) t = Df(te)e.
5. (Conclusion.) By step 4 the integrands agree pointwise, so in every integrand of (3.1) Df(te)e may be replaced by deriv (fun s => f(s•e)) t. This gives Σ_{e∈F} ∫_{(0,∞)} G_e(t)·deriv (fun s => f(s•e)) t dt = 0. ∎

## Key steps

1. f̂(x) := constOfIsEmpty(f(x)) is a test 0-form, because constOfIsEmptyLIE is continuous linear and maps 0 to 0.
2. extDeriv_constOfIsEmpty: (d f̂)(x)[v] = Df(x)v.
3. ∂C = 0 and boundary_apply give 0 = C(d f̂), which by the ray representation equals Σ_e ∫_{(0,∞)} G_e(t)·Df(te)e dt.
4. Chain rule: deriv (s ↦ f(s e)) t = Df(te)e; substituting this gives the claim.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `rg -n "theorem extDeriv_constOfIsEmpty|def constOfIsEmptyLIE|theorem integral_Ioi_of_hasDerivAt_of_tendsto |theorem HasCompactSupport.comp_isClosedEmbedding|structure ContDiffBump|theorem contDiff_norm_sq|theorem IsCompact.exists_forall_le'|theorem setIntegral_eq_zero_of_forall_eq_zero|theorem Filter.EventuallyEq.deriv_eq|theorem ae_restrict_neBot|theorem HasCompactSupport.is_zero_at_infty|theorem Continuous.integrable_of_hasCompactSupport|theorem HasCompactSupport.deriv|theorem norm_sub_sq_real|theorem ContDiff.continuous_deriv |theorem eventually_all_finset|theorem one_of_mem_closedBall|theorem zero_of_le_dist|theorem integral_congr_ae|theorem Finset.sum_eq_single_of_mem" <snapshot>/mathlib/Mathlib`
- `rg -n "comp_isClosedEmbedding|is_zero_at_infty" <snapshot>/mathlib/Mathlib/Topology/Algebra/Support.lean; rg -n "is_one_at_infty" <snapshot>/mathlib/Mathlib`
- `rg -n -i "constancy|du_bois|duBois|ray_ftc|ray_cutoff|boundary_ray" <snapshot>/project/GMT`
- `rg -n "extDeriv_constOfIsEmpty|constOfIsEmptyLIE|exteriorDerivativeTestOn" <snapshot>/project/GMT (no match)`
- `grep -n "boundary_apply" .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/*.lean; sed -n 100,345p .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean; sed -n 1,140p .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `python3 -I scans of dag.json: nodes under the parent one_dim_cones-a1 (status, lean_name, lean_statement, depends_on); lean_statement substrings 'deriv (fun s', 'constOfIsEmpty', 'exteriorDerivativeTestOn', 'TestFormOn (univ : Set (Euclid P)) 0', 'fderiv ℝ f x v', 'C.boundary', 'HasCompactSupport f →'; membership of idtp_fons_odc_rc_boundary_ray_test / idtp_fons_odc_rc_ray_cutoff / idtp_fons_odc_rc_ray_ftc among the 2106 lean_names (all absent); grep -rl idtp_fons_odc_rc_ nodes GMT .lake/packages/simongmt/Poincare (no match)`
- `git show 75f499358:GMT/Ch07/Submission.lean (odc_zero_testForm, odc_constancy_deriv_ray, odc_constancy_exact, odc_constancy_integral_deriv, odc_constancy_cutoff, odc_ray_constancy)`
- `grep -n in /runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/{leaf_verification.py,runtime.py,prompts.py,lean_contract.py}: check_source_delta, _decompose max_depth, _existing_lean_name_problem, validate_lean_statement`
- `sed -n 569,604p book/chapter-06.txt (Simon 2.34 Constancy Theorem)`
- `lake env lean /tmp/rc_split/check/Types.lean; lake env lean /tmp/rc_split/check/Assembly.lean; lake env lean /tmp/rc_split/check/Candidate.lean; python3 -I /tmp/rc_split/scripts/leafcheck2.py GMT/Ch07/Submission.lean /tmp/rc_split/check/Assembly.lean`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Calculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Order/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Deriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Deriv/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Deriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/problem.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-a005df247f/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-0e9a4f203404/_recursive_lean/lean_contract.py`
- `/tmp/rc_split/draft.lean`
- `/tmp/rc_split/check/Types.lean`
- `/tmp/rc_split/check/Assembly.lean`
- `/tmp/rc_split/check/Candidate.lean`

Pins match. The snapshot manifest records project b4d606db and Mathlib 25730c7c, which are the workspace HEAD and .lake/packages/mathlib; SimonGMT is 2b366308. The workspace Contract.lean and Submission.lean are byte-identical.
The snapshot Mathlib supplies every library fact the children need:
- extDeriv_constOfIsEmpty (Analysis/Calculus/DifferentialForm/Basic.lean:143)
- constOfIsEmptyLIE (Analysis/Normed/Module/Alternating/Basic.lean:319)
- integral_Ioi_of_hasDerivAt_of_tendsto (MeasureTheory/Integral/IntegralEqImproper.lean:786)
- HasCompactSupport.comp_isClosedEmbedding (Topology/Algebra/Support.lean:290), and is_zero_at_infty via to_additive of is_one_at_infty (:352)
- ContDiffBump with one_of_mem_closedBall and zero_of_le_dist (Analysis/Calculus/BumpFunction/Basic.lean:70, :137, :163)
- contDiff_norm_sq (Analysis/InnerProductSpace/Calculus.lean:140)
- IsCompact.exists_forall_le' (Topology/Order/Compact.lean:236)
- setIntegral_eq_zero_of_forall_eq_zero (MeasureTheory/Integral/Bochner/Set.lean:357)
- Filter.EventuallyEq.deriv_eq (Analysis/Calculus/Deriv/Basic.lean:638)
- HasCompactSupport.deriv (Analysis/Calculus/Deriv/Support.lean:60)
- ContDiff.continuous_deriv (Analysis/Calculus/ContDiff/Deriv.lean:108)
- Continuous.integrable_of_hasCompactSupport (MeasureTheory/Function/LocallyIntegrable.lean:622)
- ae_restrict_neBot (MeasureTheory/Measure/Restrict.lean:710)
- norm_sub_sq_real (Analysis/InnerProductSpace/Basic.lean:437)
- eventually_all_finset (Order/Filter/Finite.lean:258)
SimonGMT supplies GeometricCurrentOn.boundary_apply (Chapter06/Currents.lean:333), exteriorDerivativeTestOn (:193) and TestFormOn (:123).
The snapshot project has no usable lemma for any child. GMT/Ch06/Contract.lean:213 only states the top-dimensional ConstancyTheorem Prop under a sorry'd main_theorem, and GMT/Ch08 has only a varifold constancy Prop. Searches for constOfIsEmpty and exteriorDerivativeTestOn in project/GMT found nothing. No DAG node, accepted or active, states any of the three child types; the closest, idtp_pc_boundary_weak_derivative, concerns plane representations and has a different type. The three proposed names are unused.
Lean results:
- All three child types elaborate in the frozen context.
- All three are proved inside the frozen Submission.lean with axioms [propext, Classical.choice, Quot.sound] only.
- Each passes a copy of the workflow's leaf-delta checker as a single appended theorem.
- The selected frozen type follows from the three children plus the frozen sibling type idtp_fons_odc_du_bois_reymond (stubbed); the only sorryAx comes from that stub.
