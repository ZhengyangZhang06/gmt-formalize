# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.density_gap-a1`
- Child DAG node: `root.dimension_reduction_results-a1.density_gap-a1.origin_regularity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Simon Ch. 7, Lemma 1.2 (minimizing currents are stationary; chapter-07.txt lines 29–60), here in the flat case N = ℝ^P, followed by Allard's Regularity Theorem (Ch. 5, 5.2; chapter-05.txt lines 1008–1032) applied at the origin. This is how the book itself uses them in 7.4.3 (chapter-07.txt lines 626–631: "by Allard's Theorem 5.2 of Ch. 5 we have y ∈ reg T … (1.2 justifies the use of 5.2 of Ch. 5)") and in the proof of 7.4.4(8) (lines 673–675).
Every analytic input is a sibling of this decomposition. E and K are comparator-accepted declarations, reused by exact name and type; F, G and J are siblings declared under fresh names; no unaccepted declaration of another DAG branch is used:
- E = imrep_mass_support (Submission.dor_imrep_massOn_eq_measure_and_support, comparator-accepted);
- F = c1_pushforward (Submission.dimred_cdg_c1_diffeo_pushforward_im);
- G = first_variation_bound (Submission.dimred_cdg_pushforward_massOn_le_first_variation);
- J = allard_graph (Submission.dimred_cdg_allard_bounded_curvature_graph);
- K = graph_cycle_regular (Submission.dor_graph_supported_cycle_regular, comparator-accepted).
Notation: for R = (M, θ, ξ) ∈ IMRep, μ := R.measure = θH^j⌞M and δV(X) := R.firstVariation X = ∫_M θ div_M X dH^j. B_r(x) is the open ball (Lean ball) and B̄_r(x) the closed ball; spt X := tsupport X; ω_j := unitBallVolume j; M_W := massOn; spt C := C.support.
1. (Dimensions and constants.) Since j ≤ P, write P = j + k with k := P − j (in Lean: obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le), so ℝ^P is literally Euclid (j + k). Apply J with n := j ≥ 1, this k and ε := 1/4. It yields δ₀ > 0 and γ ∈ (0, 1], depending only on j and k, i.e. only on P and j. Put δ := δ₀ > 0. This δ is fixed before C is chosen, as the statement requires.
2. (Representation, mass and support.) Let C satisfy the hypotheses for this δ. IsMinimizingIn C univ contains IsIntegerMultiplicity C, so there is R = (M, θ, ξ) ∈ IMRep univ j with R.Represents C. Apply E with U := ℝ^P (open), T := C and R:
- (E1) M_W(C) = μ(W) for every open W ⊆ ℝ^P;
- (E2) spt C = ℝ^P ∩ spt μ = spt μ.
Since 0 ∈ spt C by hypothesis, 0 ∈ spt μ.
3. (Stationarity: δV(X) = 0 for every C¹ vector field X : ℝ^P → ℝ^P with compact support.) This is Simon 7.1.2 for N = ℝ^P. Fix such an X and put K := spt X, a compact set.
 3.1 DX is continuous with compact support, so A := sup_x ‖DX(x)‖ is finite, and A ≥ 0. By the mean value inequality on the convex set ℝ^P, |X(x) − X(y)| ≤ A|x − y| for all x, y.
 3.2 For t ∈ ℝ let φ_t(y) := y + tX(y). Each φ_t is C¹. φ_t = id outside K, since X = 0 there. Dφ_t(x) = I + tDX(x), so ‖Dφ_t(x) − I − tDX(x)‖ = 0 ≤ ε|t| for all ε > 0, t and x.
 3.3 Let |t|A < 1.
 (a) φ_t is injective: φ_t(x) = φ_t(y) gives x − y = t(X(y) − X(x)), so |x − y| ≤ |t|A|x − y|, whence x = y.
 (b) φ_t is surjective: |(φ_t(x) − φ_t(y)) − (x − y)| = |t||X(x) − X(y)| ≤ |t|A|x − y|. So φ_t approximates the identity isomorphism of ℝ^P on all of ℝ^P with constant |t|A < 1 = ‖id⁻¹‖⁻¹, and φ_t is onto by Mathlib's ApproximatesLinearOn.surjective with f' = ContinuousLinearEquiv.refl. For P = 0 the space is a single point. Equivalently, for each y the map x ↦ y − tX(x) is a contraction of the complete space ℝ^P, and its fixed point x satisfies φ_t(x) = y.
 (c) Dφ_t(x) is injective for every x: (I + tDX(x))v = 0 gives |v| = |t||DX(x)v| ≤ |t|A|v|, so v = 0.
 (d) φ_t(K) ⊆ K: if x ∈ K and φ_t(x) ∉ K, then φ_t(φ_t(x)) = φ_t(x) because φ_t = id off K. By (a), φ_t(x) = x, which contradicts x ∈ K.
 3.4 (The open set W.) Let K' := K ∪ {0}, a compact set, and W := {y : dist(y, K') < 1}, an open set.
- K ⊆ W and B_1(0) ⊆ W.
- closure(W) ⊆ {y : dist(y, K') ≤ 1}, which is compact because ℝ^P is proper. Hence W ⊂⊂ ℝ^P (CompactlyContained W univ).
- μ is finite on compact sets: for compact Q, μ(Q) = ∫_{M∩Q} θ dH^j < ∞ by IMRep.locallyIntegrable_mult (via withDensity_apply and Measure.restrict_restrict). So μ(W) ≤ μ({dist(·, K') ≤ 1}) < ∞.
- μ(W) ≥ μ(B_1(0)) > 0, because 0 ∈ spt μ (step 2).
Put m := μ(W) ∈ (0, ∞).
 3.5 (First-variation bound.) G applies with U := ℝ^P, this W, R, X and the family φ. Its hypotheses hold: W is open; μ(W) ≠ ∞; X is C¹ with compact support; spt X = K ⊆ W; every φ_t is C¹ and equals the identity off spt X; and the derivative condition holds by 3.2. Hence for every ε > 0 there is δ_G > 0 with the following property. For every |t| < δ_G and every S ∈ 𝒟_j(ℝ^P) with S(ω) = ∫_M θ(x)ξ(x)(ω(φ_t x)∘Dφ_t(x)) dH^j(x) for all ω ∈ 𝒟^j(ℝ^P), we have M_W(S) ≤ ofReal(m + t·δV(X) + ε|t|).
 3.6 (Choice of t.) Suppose a := δV(X) ≠ 0. Take ε := |a|/2 and δ_G from 3.5. Put s := min{δ_G/2, 1/(2(A + 1)), m/|a|} > 0, and t := −s if a > 0, t := s if a < 0. Then:
- |t| = s < δ_G and |t|A < 1;
- ta = −s|a|;
- 0 < s|a| ≤ m.
 3.7 (The competitor.) F applies with U := ℝ^P (open), K, T := C, R and φ := φ_t. Its hypotheses hold: R represents C; K is compact; and φ_t is C¹, bijective, has injective derivative everywhere and equals the identity off K (3.2–3.3). It gives an integer multiplicity S ∈ 𝒟_j(ℝ^P) with ∂S = 0 (because ∂C = 0) and S(ω) = ∫_M θ ξ(ω(φ_t x)∘Dφ_t(x)) dH^j for all ω.
 3.8 (spt(S − C) ⊆ K.) Let y ∉ K and choose r > 0 with B_r(y) ∩ K = ∅ (K is closed). Let ω ∈ 𝒟^j(ℝ^P) with spt ω ⊆ B_r(y). Using C(ω) = R.action(ω), (S − C)(ω) = S(ω) − C(ω) = ∫_M θ(x)[ξ(x)(ω(φ_t x)∘Dφ_t(x)) − ξ(x)(ω(x))] dH^j(x). The two integrands coincide at every x:
- if x ∈ K, then φ_t(x) ∈ K by 3.3(d), so ω(φ_t x) = 0 = ω(x), since ω vanishes off B_r(y) and B_r(y) misses K;
- if x ∉ K, then φ_t = id on the open neighbourhood ℝ^P ∖ K of x, so φ_t(x) = x and Dφ_t(x) = I.
Hence S − C vanishes on B_r(y), an open set with compact closure in ℝ^P. So y lies in the zero region of S − C, and y ∉ spt(S − C). Thus spt(S − C) ⊆ K. Since spt(S − C) is closed (the complement of the open zero region) and K is compact, spt(S − C) is compact. Also spt(S − C) ⊆ K ⊆ ℝ^P ∩ W.
 3.9 (Minimality.) The competitor S is admissible in Simon 7.1.1:
- ∂S = ∂C, both being 0 (j ≥ 1);
- S is integer multiplicity;
- W is open with W ⊂⊂ ℝ^P;
- spt(S − C) is a compact subset of ℝ^P ∩ W.
So IsMinimizingIn C univ gives M_W(C) ≤ M_W(S). By (E1), M_W(C) = μ(W) = ofReal(m). By 3.5–3.6, M_W(S) ≤ ofReal(m + ta + (|a|/2)|t|) = ofReal(m − s|a|/2). Since 0 < m − s|a|/2 < m, we get ofReal(m − s|a|/2) < ofReal(m), a contradiction. Hence δV(X) = 0.
4. (Closed-ball mass bound.) For ρ ∈ (1/2, 1], B̄_{1/2}(0) ⊆ B_ρ(0). By (E1) and the hypothesis of the statement, μ(B̄_{1/2}(0)) ≤ μ(B_ρ(0)) = M_{B_ρ(0)}(C) ≤ (1 + δ₀)ω_jρ^j. The right side is continuous in ρ, with a finite value at ρ = 1/2 because ω_j < ∞. Letting ρ ↓ 1/2 gives μ(B̄_{1/2}(0)) ≤ (1 + δ₀)ω_j(1/2)^j.
5. (Allard at the origin.) Apply J, with the δ₀ and γ of step 1, to U := W := ℝ^P, R, H :≡ 0, κ := 0, ρ := 1/2 and z := 0. Its hypotheses hold:
- W is open and W ⊆ U;
- B̄_{1/2}(0) ⊆ W;
- H is measurable with |H| ≤ κ = 0;
- for every C¹ compactly supported X, δV(X) = 0 = −∫⟨X, H⟩ dμ (step 3);
- 0 ∈ spt μ (step 2);
- μ(B̄_{1/2}(0)) ≤ (1 + δ₀)ω_j(1/2)^j (step 4);
- κρ = 0 ≤ δ₀.
Put r := γ/2 > 0. J gives:
- linear isometries ι : ℝ^j → ℝ^P and ι' : ℝ^k → ℝ^P with ⟨ιv, ι'w⟩ = 0 for all v, w;
- u : ℝ^j → ℝ^k with u(0) = 0, u of class C¹ on B_r(0) ⊆ ℝ^j and ‖Du(v)‖ ≤ 1/4 there;
- spt μ ∩ B_r(0) = Φ(B_r(0)) ∩ B_r(0), where Φ(v) := 0 + ιv + ι'u(v).
6. (The graph over a cylinder.) Put σ := r/4 > 0 and Cyl := {0 + ιv + ι'w : |v| < σ, |w| < σ}.
 6.1 For v ∈ B_r(0), |u(v)| ≤ |v|/4. Indeed u is differentiable at every point of the open convex ball B_r(0), being C¹ there, with ‖Du‖ ≤ 1/4. So the mean value inequality gives |u(v) − u(0)| ≤ |v − 0|/4, and u(0) = 0.
 6.2 |ιv + ι'w| ≤ |ιv| + |ι'w| = |v| + |w|. Hence Cyl ⊆ B_{2σ}(0) ⊆ B_r(0).
 6.3 If ιv + ι'w = ιv' + ι'w', then v = v' and w = w'. Indeed ι(v − v') = ι'(w' − w), so |ι(v − v')|² = ⟨ι(v − v'), ι'(w' − w)⟩ = 0. Hence |v − v'| = |ι(v − v')| = 0. Then ι'w = ι'w', and ι' is injective.
 6.4 spt μ ∩ Cyl = Φ(B_σ(0)).
- (⊆) Let x = ιv + ι'w ∈ spt μ with |v|, |w| < σ. By 6.2, x ∈ B_r(0), so by step 5, x = Φ(v') for some v' ∈ B_r(0). By 6.3, v' = v and w = u(v). So x = Φ(v) with v ∈ B_σ(0).
- (⊇) Let |v| < σ. By 6.1, |u(v)| ≤ |v|/4 < σ, so Φ(v) ∈ Cyl ⊆ B_r(0). Also v ∈ B_r(0). So Φ(v) ∈ Φ(B_r(0)) ∩ B_r(0) = spt μ ∩ B_r(0) by step 5.
7. (Regularity.) Apply K with n := j ≥ 1, k, U := ℝ^P (open), T := C, R, ι, ι', u, z := 0 and s := h := σ. Its hypotheses hold:
- R represents C, and ∂C = 0;
- ⟨ιv, ι'w⟩ = 0 for all v, w, and σ > 0;
- u is C¹ on B_σ(0) ⊆ B_r(0), and u(0) = 0;
- Cyl ⊆ ℝ^P, and spt μ ∩ Cyl = Φ(B_σ(0)) (6.4);
- 0 ∈ spt C.
Hence 0 ∈ reg C (regularSet C). ∎
Formalization note. This proof was re-checked for this revision in the scratch file /tmp/dg8/lean/OriginRegular.lean, theorems dg8_stationary (step 3) and dg8_origin_regular (steps 1–7):
- Build: lake env lean against the frozen GMT.Ch07.Submission (project b4d606d, Mathlib 25730c7c, simongmt 2b36630).
- Hypotheses: exactly the frozen types of E, F, G, J, K, matched character for character; no other hypothesis and no sorry.
- #print axioms: propext, Classical.choice, Quot.sound.
- /tmp/dg8/lean/Linked.lean applies the same proof to the declarations Submission.dor_imrep_massOn_eq_measure_and_support, Submission.dimred_cdg_c1_diffeo_pushforward_im, Submission.dimred_cdg_pushforward_massOn_le_first_variation, Submission.dimred_cdg_allard_bounded_curvature_graph and Submission.dor_graph_supported_cycle_regular. These are declared there with their frozen types, and the application proves Submission.dimred_cdg_minimizing_origin_regular.
- Two inessential simplifications in the scratch build: 3.1 takes A := max(sup‖DX‖, 0), and 3.6 takes s := min{δ_G/2, 1/(2(A + 1))} without the cap m/|a|. The cap is not needed: ENNReal.ofReal_lt_ofReal_iff needs only 0 < m, so ofReal(m − s|a|/2) < ofReal(m) holds either way.
Lemmas used, by step:
- 3.1: Continuous.bounded_above_of_compact_support with hX.continuous_fderiv one_ne_zero and HasCompactSupport.fderiv; Convex.norm_image_sub_le_of_norm_fderiv_le.
- 3.2: (hasFDerivAt_id x).add ((hX.differentiable one_ne_zero x).hasFDerivAt.const_smul t); image_eq_zero_of_notMem_tsupport for φ_t = id off K.
- 3.3: ApproximatesLinearOn.surjective with ContinuousLinearEquiv.refl and ContinuousLinearMap.nnnorm_id; the Subsingleton case covers P = 0.
- 3.4: W := Metric.thickening 1 (insert 0 (tsupport X)), with closure_thickening_subset_cthickening and IsCompact.cthickening. Finiteness by IMRep.measure, withDensity_apply, Measure.restrict_restrict and R.locallyIntegrable_mult; positivity by Measure.mem_support_iff_forall.
- 3.8: the zero region is witnessed by ball y r with isCompact_closedBall and closure_ball_subset_closedBall; fderiv_of_notMem_tsupport gives DX = 0, hence Dφ_t = I, off K.
- 3.9: ENNReal.ofReal_lt_ofReal_iff.
- 4: ge_of_tendsto, Ioo_mem_nhdsGT and ENNReal.Tendsto.const_mul.
- 6: LinearIsometry.norm_map, real_inner_self_eq_norm_sq, sub_eq_sub_iff_add_eq_add, add_left_cancel and LinearIsometry.injective.

## Key steps

1. Write P = j + k and take δ := δ₀ from the sibling allard_graph with n = j and ε = 1/4; δ₀ and γ depend only on (P, j).
2. A minimizing C has an integer multiplicity representation R; the sibling imrep_mass_support gives M_W(C) = μ_R(W) for open W and spt C = spt μ_R, so 0 ∈ spt μ_R.
3. Flat Simon 7.1.2: for X ∈ C¹_c, φ_t = id + tX is a C¹ bijection with injective derivative for |t|·sup‖DX‖ < 1. The sibling c1_pushforward gives integer multiplicity competitors S_t with spt(S_t − C) ⊆ spt X. Minimality on W ⊃ spt X ∪ B_1(0), with M_W(C) = μ(W) > 0, combined with the sibling first_variation_bound, forces δV(X) = 0.
4. The open-ball mass hypothesis on (1/2, 1] gives μ(B̄_{1/2}(0)) ≤ (1 + δ₀)ω_j(1/2)^j in the limit.
5. The sibling allard_graph, applied with H ≡ 0, κ = 0, ρ = 1/2 and z = 0, makes spt μ near 0 the graph of a C¹ map u with u(0) = 0 and |Du| ≤ 1/4.
6. Orthogonality of ι and ι' and |u(v)| ≤ |v|/4 identify spt μ in the cylinder of radius γ/8 with the graph; the sibling graph_cycle_regular then gives 0 ∈ reg C.

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD; git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `rg -l -e 'dimred_cdg_(eq_zero_of_lt_degree|im_cone_ball_mass|c1_diffeo_pushforward_im|pushforward_massOn_le_first_variation|harmonic_affine_approximation|allard_bounded_curvature_graph|minimizing_origin_regular)' -g '*.lean' local-references/123e8435b4a2469b lake-packages-25730c7c/simongmt/Poincare lake-packages-25730c7c/mathlib/Mathlib workspaces/gmt-ch07/GMT (exit 1: no match)`
- `grep -c -E '<same pattern>' dag.json (0); grep -l -E '<same pattern>' over the 780 workspaces/.swarm-worktrees/*/gmt-ch07/GMT/Ch07/Submission.lean (no match); git log --all --oneline -S dimred_cdg_ (only bbbfd3b8, which mentions dimred_cdg_weak_limit_cone, not a proposed name)`
- `python3 -I /tmp/dg8scripts/check_candidates.py dag.json (git show <candidate>:GMT/Ch07/Submission.lean for e183b985, d49dda91, 36b2d372, 2fd8f6ff, 8a6855aa, 4d9f2899, 01ae2c59, 428db72e: each declares theorem Submission.<lean_name> : <frozen type> := verbatim)`
- `python3 -I /tmp/dg8scripts/name_check.py <run> <decomposition> for v6, v7 and v8 (replay of Runtime._existing_lean_name_problem on dag.json) and replay of Runtime._topological`
- `python3 inspection of dag.json: statuses, candidate commits and frozen types of every node whose lean_statement equals a child type (including the fvmb_* children of first_variation_mass_bound-a1 and the codim1_ldr_ duplicates); this node's record (decomposing, attempt 8, children [])`
- `sed -n '1440,1560p;2355,2385p;6585,6660p' /runtime/flows/gmt-claude-b731e326000c/_recursive_lean/runtime.py; sed -n '60,260p' /runtime/flows/gmt-claude-b731e326000c/_recursive_lean/store.py (_decompose, _accepted_checkpoint, _existing_lean_name_problem, _reference_use_problem, Store.refresh, Store.update)`
- `cat cluster-state/logs/gmt-ch07/e39b4162870940da8110ef2d3c8bdbfa.log; ls nodes/root-minimizing-implies-stationary-a1-first-variation-mass-bound-a1/ (accepted-candidate.json at 07:57Z)`
- `python3 diff of nodes/root-dimension-reduction-results-a1-density-gap-a1/decomposition-v6.json and decomposition-v7.json; cat decomposition-audit-v1..v6.json`
- `sed -n '620,635p;25,62p' book/chapter-07.txt (Simon 7.1.2 and the use of Allard 5.2 in 7.4.3)`
- `PATH=<toolchain lean-4.35.0-rc3>/bin:$PATH lake env lean /tmp/dg8/lean/{Types,Linked,Assembly,HighDegreeZero,ConeBallMass,OriginRegular,HarmonicConclusion}.lean (each with #print axioms); python3 -I /tmp/dg8scripts/check_frozen.py dag.json`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-density-gap-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-density-gap-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-density-gap-a1/decomposition-v6.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-density-gap-a1/decomposition-v7.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-density-gap-a1/decomposition-audit-v6.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-density-gap-a1/decomposition-review-receipt-v5.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-first-variation-mass-bound-a1/accepted-candidate.json`
- `/runtime/flows/gmt-claude-b731e326000c/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-b731e326000c/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/cluster-state/logs/gmt-ch07/e39b4162870940da8110ef2d3c8bdbfa.log`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/dg8/lean/Types.lean`
- `/tmp/dg8/lean/Linked.lean`
- `/tmp/dg8/lean/Assembly.lean`
- `/tmp/dg8/lean/HighDegreeZero.lean`
- `/tmp/dg8/lean/ConeBallMass.lean`
- `/tmp/dg8/lean/OriginRegular.lean`
- `/tmp/dg8/lean/HarmonicConclusion.lean`
- `/tmp/dg8scripts/check_frozen.py`
- `/tmp/dg8scripts/check_candidates.py`
- `/tmp/dg8scripts/name_check.py`

Pins match: the manifest records project b4d606d and Mathlib 25730c7c, which equal the workspace HEAD and the snapshot and package Mathlib; simongmt is at 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.
- Reuse: cone_current_imrep_measure_smul_image (e183b985), dor_imrep_massOn_eq_measure_and_support (d49dda91), imrep_approxTangent_starProjection_aesm (36b2d372), covectorEuclideanNorm_gram_bounds (2fd8f6ff) and dor_graph_supported_cycle_regular (8a6855aa) are accepted. Each has a character-identical frozen type and is declared verbatim in its candidate commit. The resolved dependencies dimred_im_mass_measure (01ae2c59) and dimred_regular_point_density (428db72e) are also accepted and declared verbatim.
- pushforward_action_massOn_le_first_variation (4d9f2899) is accepted with the identical type, but the runtime refused it for this parent. The child therefore uses the fresh name dimred_cdg_pushforward_massOn_le_first_variation, and its six fvmb_* helpers are cited only as a formalization aid.
- Names: the seven fresh dimred_cdg_ names occur nowhere in the snapshot, SimonGMT, Mathlib, the workspace GMT sources, dag.json, the 780 swarm-worktree Submission files or git history. Replaying the runtime name check and the topological sort on v8 reports no problem.
- Lean: all fifteen types elaborate. Linked.lean proves Submission.dimred_cone_density_gap from the actual child declarations, with sorry only in the eleven leaf stubs. The conditional checks (assembly, high_degree_zero, cone_ball_mass, origin_regularity and harmonic_affine's Conclusion) depend only on propext, Classical.choice and Quot.sound. They do not discharge the seven new children.
