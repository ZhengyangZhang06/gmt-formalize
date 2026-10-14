# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.ray_constancy-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.one_dim_cones-a1.ray_constancy-a1.ray_cutoff-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent step 2 ('Test functions that see only one ray').
Notation: ⟨·,·⟩ is the Euclidean inner product and |·| the norm. C^∞ means ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞).
Let P, F, e₀, ψ be as in the statement.
1. (Bounds on the support of ψ.) K := tsupport ψ is compact and K ⊆ (0, ∞), so 0 < s for every s ∈ K.
 - By IsCompact.exists_forall_le' (applied to the identity, which is continuous on K, with lower bound 0) there is α with 0 < α and α ≤ s for every s ∈ K. If K = ∅ any α > 0 works; otherwise α := min K > 0.
 - K is compact, hence bounded above, so there is β with s ≤ β for all s ∈ K.
 Since ψ(s) ≠ 0 implies s ∈ support ψ ⊆ K:
 (1.1) ψ(s) ≠ 0 ⇒ α ≤ s ≤ β.
2. (Choice of κ.) The set F' := {e ∈ F : ⟨e,e₀⟩² < 1} is finite, and α²(1 − ⟨e,e₀⟩²) > 0 for each e ∈ F'. Put κ := ½·min({1} ∪ {α²(1 − ⟨e,e₀⟩²) : e ∈ F'}). Then κ > 0, and
 (2.1) κ < α²(1 − ⟨e,e₀⟩²) for every e ∈ F with ⟨e,e₀⟩² < 1.
3. (The profile χ.) Let χ : ℝ → ℝ be the smooth bump function centred at 0 with inner radius κ/2 and outer radius κ (a ContDiffBump with rIn = κ/2 < rOut = κ). Then:
 - χ is C^∞;
 - χ = 1 on the closed ball of radius κ/2 about 0, so χ(0) = 1;
 - χ(s) = 0 whenever |s| ≥ κ, hence whenever s ≥ κ (because s ≤ |s|).
4. (Definition and smoothness of f.) Put f(x) := ψ(⟨x,e₀⟩)·χ(|x|² − ⟨x,e₀⟩²). The maps x ↦ ⟨x,e₀⟩ (continuous linear) and x ↦ |x|² (contDiff_norm_sq) are C^∞. Hence so are x ↦ |x|² − ⟨x,e₀⟩², its composition with χ, the composition of x ↦ ⟨x,e₀⟩ with ψ, and the product of the two. So f is C^∞.
5. (Compact support.) Let R := β² + κ + 1. Suppose f(x) ≠ 0.
 - Then ψ(⟨x,e₀⟩) ≠ 0 and χ(|x|² − ⟨x,e₀⟩²) ≠ 0.
 - By (1.1), α ≤ ⟨x,e₀⟩ ≤ β. Since α > 0, ⟨x,e₀⟩ ≥ 0 and so ⟨x,e₀⟩² ≤ β².
 - By step 3, |x|² − ⟨x,e₀⟩² < κ. Hence |x|² < β² + κ.
 - If |x| ≥ 1 then |x| ≤ |x|² < β² + κ < R. If |x| < 1 then |x| < 1 ≤ R.
 So f(x) ≠ 0 implies x ∈ closedBall(0, R). Thus f vanishes outside the compact set closedBall(0, R), and f has compact support (HasCompactSupport.intro).
6. (Values on ℝe₀.) Let s ∈ ℝ. Since |e₀| = 1, ⟨s e₀, e₀⟩ = s|e₀|² = s and |s e₀|² = s²|e₀|² = s². Hence f(s e₀) = ψ(s)·χ(s² − s²) = ψ(s)·χ(0) = ψ(s).
7. (Vanishing on the other rays.) Let e ∈ F with e ≠ e₀ and let t > 0. Put c := ⟨e,e₀⟩. Since |e| = 1, ⟨te,e₀⟩ = tc and |te|² = t², so f(te) = ψ(tc)·χ(t² − t²c²).
 - If ψ(tc) = 0, then f(te) = 0.
 - Otherwise, by (1.1), tc ≥ α > 0; as t > 0, this forces c > 0.
 - Moreover c < 1. Indeed |e − e₀|² = |e|² − 2c + |e₀|² = 2 − 2c, and |e − e₀| > 0 because e ≠ e₀, so 2 − 2c > 0.
 - Hence 0 < c < 1, so c² < 1, and (2.1) gives κ < α²(1 − c²).
 - Also t − tc = t(1 − c) > 0, so t > tc ≥ α > 0, hence t² ≥ α².
 - Therefore t² − t²c² = t²(1 − c²) ≥ α²(1 − c²) > κ. By step 3 the χ-factor vanishes, so f(te) = ψ(tc)·0 = 0.
Steps 4–7 show that f has all the required properties. ∎

## Key steps

1. Compact tsupport ψ ⊆ (0,∞) gives 0 < α and β with ψ(s) ≠ 0 ⇒ α ≤ s ≤ β.
2. Choose 0 < κ < α²(1 − ⟨e,e₀⟩²) for the finitely many e ∈ F with ⟨e,e₀⟩² < 1, and a smooth bump χ with χ(0) = 1 and χ = 0 on [κ, ∞).
3. f(x) := ψ(⟨x,e₀⟩)·χ(|x|² − ⟨x,e₀⟩²) is C^∞ and vanishes outside closedBall(0, β² + κ + 1).
4. f(s e₀) = ψ(s)·χ(0) = ψ(s).
5. For e ∈ F∖{e₀} and t > 0, ψ(tc) ≠ 0 forces 0 < c := ⟨e,e₀⟩ < 1 and t > α, so t²(1 − c²) > κ and f(te) = 0.

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
