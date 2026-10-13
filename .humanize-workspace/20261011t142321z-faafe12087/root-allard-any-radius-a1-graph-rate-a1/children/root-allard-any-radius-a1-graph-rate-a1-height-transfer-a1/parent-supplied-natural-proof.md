# Parent-supplied natural-language proof

- Parent DAG node: `root.allard_any_radius-a1.graph_rate-a1`
- Child DAG node: `root.allard_any_radius-a1.graph_rate-a1.height_transfer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation as in the statement. (L.) refers to la_basics and (P.) to plane_projections. Integrals of [0, infinity]-valued functions are lower (Lebesgue) integrals. They are monotone under a.e. inequalities and in the domain for arbitrary functions, and a finite constant factor can be pulled out.

0. If R <= 0 then Omega is empty and the left side is 0. Assume R > 0, so 0 lies in Omega.

1. Borel representative. Since y -> p_y is mu-a.e. strongly measurable, there is a strongly measurable map p~ : R^(n+l) -> L(R^(n+l), R^(n+l)) with p~_y = p_y for mu-a.e. y. p~ is Borel measurable, because a strongly measurable map into this finite-dimensional normed space is Borel. The set {y : p_y != p~_y} is mu-null, so it is contained in a Borel set N' with mu(N') = 0 (a measurable hull).

2. Continuity of F on Omega. u is C^1, hence continuous, on Omega. (x, y) -> graphPoint(x, y) is linear ((L1), (L3)) on a finite-dimensional space, hence continuous, and q is continuous. So F is continuous on Omega, and therefore a.e.-measurable for Lebesgue measure restricted to the open (Borel) set Omega.

3. p = p~ along the graph. Apply (E1_Omega) to the Borel function g = indicator of N' (1 on N', 0 elsewhere):
integral_Omega g(F(x)) dx <= integral_{F(Omega)} g d mu = (mu restricted to F(Omega))(N') <= mu(N') = 0.
The function x -> g(F(x)) is nonnegative, a.e.-measurable on Omega (step 2), and has zero integral, so it vanishes for a.e. x in Omega. Thus F(x) is not in N', and p_{F(x)} = p~_{F(x)}, for a.e. x in Omega.

4. Size of F. Omega is convex, u is differentiable at every point of the open set Omega, and ||Du|| <= 1/7 there. The mean value inequality and u(0) = 0 give |u(x)| = |u(x) - u(0)| <= |x|/7 for x in Omega. Since q is an isometry, (L4) gives |F(x)|^2 = |x|^2 + |u(x)|^2. Hence |x| <= |F(x)| <= (50/49)^(1/2)|x| <= 2|x| for x in Omega.

5. Pointwise inequality. Let g(y) := |y - p~_y y|^2/|y|^(n+2) >= 0 and G := ofReal o g. By (E2) and step 3, for a.e. x in Omega both p_{F(x)} = P_{Du(x)} and p_{F(x)} = p~_{F(x)} hold. Fix such an x.
- If x = 0, the integrand ofReal(|u(0) - Du(0)0|^2/|0|^(n+2)) = ofReal(0) = 0 (division by 0), so the inequality below is trivial.
- If x != 0, put A := Du(x), w := u(x) - A x and P := P_A = p~_{F(x)}.
  (a) By (L1), graphPoint(x, u x) = graphPoint(x + 0, A x + w) = graphPoint(x, A x) + graphPoint(0, w), so F(x) = q(graphPoint(x, A x)) + y_w with y_w := q(graphPoint(0, w)).
  (b) By (P1), P fixes q(graphPoint(x, A x)); hence F(x) - P F(x) = y_w - P y_w.
  (c) By (P2) and ||A|| <= 1/7: |w| <= (1 + 1/49)^(1/2)|y_w - P y_w| <= 2|F(x) - p~_{F(x)} F(x)|, so |w|^2 <= 4|F(x) - p~_{F(x)}F(x)|^2.
  (d) By step 4, 0 < |x| <= |F(x)| and |F(x)| <= 2|x|. So |F(x)|^(n+2) <= 2^(n+2)|x|^(n+2), i.e. 1/|x|^(n+2) <= 2^(n+2)/|F(x)|^(n+2).
  (e) Therefore |u(x) - Du(x)x|^2/|x|^(n+2) = |w|^2/|x|^(n+2) <= 2^(n+4)|F(x) - p~_{F(x)}F(x)|^2/|F(x)|^(n+2) = 2^(n+4) g(F(x)).
  (f) ofReal is monotone and ofReal(2^(n+4) t) = ofReal(2^(n+4)) ofReal(t) for t >= 0. So ofReal(|u(x) - Du(x)x|^2/|x|^(n+2)) <= ofReal(2^(n+4)) G(F(x)).

6. G is Borel. p~ is Borel, so y -> (p~_y, y) is Borel. Evaluation (M, y) -> M y is continuous, so y -> p~_y y is Borel. Then |y - p~_y y|^2, |y|^(n+2), their real quotient and ofReal are Borel.

7. Integration.
- Step 5 holds for a.e. x in Omega. By monotonicity of the lower integral and pulling out the finite constant: integral_Omega ofReal(|u(x) - Du(x)x|^2/|x|^(n+2)) dx <= ofReal(2^(n+4)) integral_Omega G(F(x)) dx.
- By (E1_Omega) for the Borel function G: integral_Omega G(F(x)) dx <= integral_{F(Omega)} G d mu.
- Since F(Omega) is contained in B^o_rho(0) and G >= 0, this is at most integral_{B^o_rho(0)} G d mu.
- Finally, G(y) = ofReal(|y - p_y y|^2/|y|^(n+2)) for mu-a.e. y (p~ = p mu-a.e.). So the last integral equals integral_{B^o_rho(0)} ofReal(|y - p_y y|^2/|y|^(n+2)) d mu(y).
Chaining these inequalities proves the claim.

## Key steps

1. Borel representative p~ = p mu-a.e. and a Borel mu-null N' containing {p != p~}
2. (E1_Omega) with g = indicator of N', plus a.e.-measurability of F on Omega, gives p(F x) = p~(F x) for a.e. x in Omega
3. Mean value inequality: |u(x)| <= |x|/7, hence |x| <= |F(x)| <= 2|x|
4. At a.e. x != 0: F(x) - P F(x) = y_w - P y_w by (P1); (Nor) gives |w| <= 2|F(x) - p~ F(x)|; so the integrand is at most 2^(n+4) G(F(x))
5. Integrate, apply (E1_Omega) to the Borel G, enlarge F(Omega) to B^o_rho(0), and replace p~ by p mu-a.e.

## Reference use

### local-project

Queries:
- `cat <snapshot>/manifest.json; cmp <snapshot>/project/GMT/Ch05/Contract.lean GMT/Ch05/Contract.lean; cmp <snapshot>/project/GMT/Ch05/Submission.lean GMT/Ch05/Submission.lean; diff GMT/Ch05/Contract.lean GMT/Ch05/Submission.lean`
- `python3 -I scan of every lean_name field in dag.json and nodes/*/*.json for the 8 any_radius_gr_* names; grep -rl any_radius_gr_ --include=*.json <run>; git grep -c any_radius_gr_ <ref> -- '*.lean' over all refs; rg -l any_radius_gr_ <snapshot>/project`
- `python3 -I dump of nodes/root-allard-any-radius-a1/decomposition-v2.json (sibling statements tangent_ae, rescaled_varifold, monotonicity_bounds, tilt_height_l1, tilt_iteration, graph_comparison, radial_height, campanato, pinching) and of this node's parent-child-handoff.json, decomposition-v1.json, decomposition-audit-v1.json, decomposition-review-receipt-v1.json`
- `sed -n 200,210p and sed -n 515,530p <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean (integral_undef, integral_eq_lintegral_of_nonneg_ae)`
- `rg -n 'theorem lintegral_mul_le_Lp_mul_Lq' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/MeanInequalities.lean; sed -n 195,215p of the same file`
- `rg -n 'eLpNorm_le_eLpNorm_mul_rpow_measure_univ' <snapshot>/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/CompareExp.lean`
- `grep -n 'theorem toReal_rpow|theorem ofReal_rpow_of_nonneg|theorem mul_rpow_of_nonneg' <snapshot>/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean; grep -n 'ofReal_norm' <snapshot>/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean`
- `grep -n 'theorem integral_map_equiv' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Bochner/*.lean; grep -n 'theorem lintegral_map_equiv' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/*.lean; grep -n 'theorem lintegral_mono_set' <snapshot>/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/*.lean`
- `lake build GMT.Ch05.Submission in /tmp/gr-v2-scratch/proj (fresh copy of the pinned snapshot project, packages symlinked to lake-packages-25730c7c)`
- `lake env lean Checks/Types.lean and Checks/TypesV2.lean (the 8 child lean_statements from v1 and from the final v2 draft, plus the selected parent type)`
- `lake env lean Checks/Iface.lean (14 sibling/child interface examples)`
- `lake env lean Checks/LpBall.lean (complete proof of the frozen lp_ball_bounds type; #print axioms)`
- `lake env lean Checks/Names.lean (#check of every Mathlib name cited in the corrected lp_ball_bounds proof)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project/GMT/Ch05/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/GMT/Ch05/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-rate-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-rate-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-rate-a1/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-rate-a1/decomposition-review-receipt-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/MeanInequalities.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Function/LpSeminorm/CompareExp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch05/.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/local-references/a7f8fcd21d5c8fc7/project`
- `/tmp/gr-v2-scratch/proj/Checks/Types.lean`
- `/tmp/gr-v2-scratch/proj/Checks/TypesV2.lean`
- `/tmp/gr-v2-scratch/proj/Checks/Iface.lean`
- `/tmp/gr-v2-scratch/proj/Checks/LpBall.lean`
- `/tmp/gr-v2-scratch/proj/Checks/Names.lean`

Snapshot
- Pinned at project ea5607598f3133b40a13241f2e51517a8c6423cd and Mathlib 25730c7c759d108ef87ab70af2342a196760f79d.
- Snapshot Contract.lean and Submission.lean are byte-identical to the workspace copies, and Submission equals Contract.

Definitions that shape the split
- scaledLpNorm = (ofReal(sigma^(p-n)) * lintegral over closedBall xi sigma of ‖H x‖ₑ^p)^(1/p).
- tiltExcess = (sigma^n)^-1 times a Bochner integral.
- lp_ball_bounds is stated for an arbitrary H (no measurability hypothesis), so its (K2) proof must split on the integrability of f = ‖H‖ itself.

Mathlib facts behind the correction
- integral_undef (Bochner/Basic.lean:204) applies to the actual integrand f.
- integral_eq_lintegral_of_nonneg_ae (:515) needs only 0 <=ᵐ f and AEStronglyMeasurable f.
- ENNReal.lintegral_mul_le_Lp_mul_Lq (MeanInequalities.lean:202) needs AEMeasurable of both factors.
- ENNReal.toReal_rpow (Pow/NNReal.lean:962) is unconditional.
- ofReal_norm replaces the deprecated ofReal_norm_eq_enorm (Normed/Group/Basic.lean:389).
- IntegrableOn.aestronglyMeasurable does not exist; Integrable.aestronglyMeasurable is cited instead.
- Change of variables along a MeasurableEquiv needs no measurability, which supports translate_identities: integral_map_equiv (Bochner/Basic.lean:1105) and lintegral_map_equiv (Lebesgue/Map.lean:94). Neither does lintegral_mono_set (Lebesgue/Basic.lean:98).

No-match results
- 'any_radius_gr_' occurs in 0 snapshot project files and in 0 .lean files on any git branch.
- In dag.json and nodes/*/*.json it occurs only in this node's own v1 proposal, audit and receipt, so the 8 names are free.

Lean
- All 8 frozen child types and the parent type elaborate.
- The full lp_ball_bounds proof compiles with only propext, Classical.choice and Quot.sound.
- The 14 interface examples compile without sorry.
