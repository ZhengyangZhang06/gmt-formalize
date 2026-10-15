# Parent-supplied natural-language proof

- Parent DAG node: `root.existence_of_minimizing_filling-a1.cone_filling-a1`
- Child DAG node: `root.existence_of_minimizing_filling-a1.cone_filling-a1.cone_parametrization-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Part F (F1–F5) of the selected parent's supplied proof together with A4 (cone Jacobian), i.e. Simon Ch. 6, 2.30 (0 ⨯ S = h_#([[(0,1)]] × S), h(t, x) = tx) and 3.10 (book/chapter-06.txt lines 528–551 and 857–865), computed on an integral Lipschitz parametrization of S. Where only the integrability of a single term is needed, the supplied bound via A2a is replaced by the cruder operator-norm bound below, which uses the integrability hypothesis (iv).

Notation. k := n + 1, so ℝ^{k+1} = Euclid (n + 2). For z ∈ ℝ^{k+1} let s(z) := (WithLp.ofLp z) 0 ∈ ℝ and τ(z) := WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) ∈ ℝ^k; ι(t, u) := WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)) is the inverse map ℝ × ℝ^k → ℝ^{k+1}. s and τ are continuous linear maps with |s(z)| ≤ ‖z‖, ‖τ(z)‖ ≤ ‖z‖, s(e_0) = 1, τ(e_0) = 0, s(e_{b+1}) = 0, τ(e_{b+1}) = e'_b, where e and e' are the standard bases of ℝ^{k+1} and ℝ^k. For vectors v_0, …, v_m let J(v) := (det[⟨v_a, v_b⟩]_{a,b})^{1/2}. For ω ∈ 𝒟^{k+1} put ‖ω‖_∞ := sup_y ‖ω(y)‖ (operator norm; finite since ω is continuous with compact support). Let L_j be a Lipschitz constant of F_j.

Step 1 (Fubini on cylinders; F2). The map z ↦ (s(z), τ(z)) is a measurable linear equivalence ℝ^{k+1} → ℝ × ℝ^k that carries Lebesgue measure to the product of the Lebesgue measures (Mathlib EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp and MeasureTheory.volume_preserving_piFinSuccAbove (fun _ => ℝ) 0). Hence, for Borel A ⊆ ℝ^k, the cylinder Cyl(A) := {z : s(z) ∈ (0, 1), τ(z) ∈ A} is Borel; ∫⁻_{Cyl(A)} f = ∫⁻_A ∫⁻_{(0,1)} f(ι(t, u)) dt du for every Borel f : ℝ^{k+1} → [0, ∞] (Tonelli); and ∫_{Cyl(A)} f = ∫_A ∫_{(0,1)} f(ι(t, u)) dt du for every real f integrable on Cyl(A) (Fubini). (These three facts are the comparator-accepted lemma cmcdt_lpi_cyl_fubini, which a decomposition of this node may reuse at its identical type.)

Step 2 (radius and retraction; F1). spt S is compact, so there is ρ > 0 with spt S ⊆ ball(0, ρ). Let r_ρ(y) := y if ‖y‖ ≤ ρ and r_ρ(y) := (ρ/‖y‖)y otherwise; r_ρ is the nearest-point projection onto the closed convex ball B̄ := closedBall(0, ρ), and it is 1-Lipschitz. Indeed, with p := r_ρ(x) one has ⟨x − p, z − p⟩ ≤ 0 for every z ∈ B̄ (if ‖x‖ ≤ ρ then x − p = 0; otherwise x − p = (1 − ρ/‖x‖)x and ⟨x, z⟩ ≤ ρ‖x‖ = ⟨x, p⟩). For q := r_ρ(y) this gives ⟨x − p, q − p⟩ ≤ 0 and ⟨y − q, p − q⟩ ≤ 0; adding, ‖p − q‖² ≤ ⟨x − y, p − q⟩ ≤ ‖x − y‖‖p − q‖, so ‖p − q‖ ≤ ‖x − y‖. Put F̂_j := r_ρ ∘ F_j: it is L_j-Lipschitz, ‖F̂_j‖ ≤ ρ, and F̂_j = F_j on the open set O_j := F_j⁻¹(ball(0, ρ)), which contains A_j by (vi).

Step 3 (definitions). Let σ(t) := min(max(t, 0), 1) (1-Lipschitz, values in [0, 1], σ(t) = t for t ∈ [0, 1]). Define G_j(z) := σ(s(z)) • F̂_j(τ(z)), B_j := Cyl(A_j) and w_j(z) := g_j(τ(z)).
 (a) B_j is Borel (Step 1) and w_j is measurable (g_j measurable, τ continuous).
 (b) G_j is Lipschitz: ‖G_j(z) − G_j(z')‖ ≤ |σ(s(z)) − σ(s(z'))|·‖F̂_j(τ(z))‖ + σ(s(z'))·‖F̂_j(τ(z)) − F̂_j(τ(z'))‖ ≤ ρ|s(z) − s(z')| + L_j‖τ(z) − τ(z')‖ ≤ (ρ + L_j)‖z − z'‖.
 (c) (w_j : ℝ) is integrable on B_j: by Step 1 (Tonelli), ∫⁻_{B_j} |w_j| = ∫⁻_{A_j} ∫⁻_{(0,1)} |g_j(u)| dt du = ∫⁻_{A_j} |g_j| < ∞ by (iv).

Step 4 (derivative on B_j; F3). Let z ∈ B_j, t := s(z) ∈ (0, 1), u := τ(z) ∈ A_j. The set {z' : s(z') ∈ (0, 1), τ(z') ∈ O_j} is an open neighbourhood of z on which G_j(z') = s(z') • F_j(τ(z')). F_j is differentiable at u by (v), and s, τ are linear, so by the product rule G_j is differentiable at z with DG_j(z)h = s(h)·F_j(u) + t·DF_j(u)(τ(h)). Hence DG_j(z)e_0 = F_j(u) and DG_j(z)e_{b+1} = t·DF_j(u)e'_b, i.e. ∂G_j(z) = Fin.cons (F_j u) (t • ∂F_j(u)).

Step 5 (integrand). For ω ∈ 𝒟^{k+1} and z ∈ B_j (t, u as in Step 4), multilinearity in the last k arguments gives ω(G_j z)(∂G_j z) = ω(t • F_j u)(Fin.cons (F_j u) (t • ∂F_j u)) = t^k·ω(t • F_j u)(Fin.cons (F_j u) (∂F_j u)).

Step 6 (cone Jacobian; A4). Let a, w_1, …, w_k ∈ ℝ^P and t ≥ 0.
 (a) J(a, tw_1, …, tw_k) = t^k J(a, w_1, …, w_k): the Gram matrix of (a, tw) is D·Gram(a, w)·D with D := diag(1, t, …, t), so its determinant is t^{2k} det Gram(a, w).
 (b) J(a, w) ≤ ‖a‖·J(w). If w is linearly dependent, so is (a, w), and both Gram determinants vanish (Gram(v)c = 0 for a nonzero c with Σ c_a v_a = 0). Otherwise let π be the orthogonal projection onto W := span(w) and a' := a − πa = a − Σ_i c_i w_i. Replacing a by a' is the column operation Gram(a', w) = Eᵀ·Gram(a, w)·E with E unipotent (det E = 1), and since a' ⊥ W the matrix Gram(a', w) is block diagonal with blocks ‖a'‖² and Gram(w). Hence det Gram(a, w) = ‖a'‖²·det Gram(w) ≤ ‖a‖²·det Gram(w).
 Consequently, for z ∈ B_j (t, u as in Step 4), JG_j(z) = J(F_j u, t∂F_j u) = t^k J(F_j u, ∂F_j u) ≤ t^k‖F_j u‖·JF_j(u) ≤ ρ·JF_j(u), because 0 < t < 1 and ‖F_j u‖ < ρ by (vi).

Step 7 (total weight; F5). By Step 6, Step 1 (Tonelli) and (vii): Σ_j ∫⁻_{B_j} |w_j|·JG_j ≤ Σ_j ∫⁻_{A_j} ∫⁻_{(0,1)} |g_j(u)|·ρ·JF_j(u) dt du = ρ·Σ_j ∫⁻_{A_j} |g_j|·JF_j < ∞.

Step 8 (representation; F4). Fix ω ∈ 𝒟^{k+1} and take γ from (ix): R(ω) = S(γ) and γ(x)(v) = ∫_0^1 t^k ω(tx)(Fin.cons x v) dt for x ∈ spt S. By (viii), HasSum (j ↦ I_j) (S(γ)) with I_j := ∫_{A_j} g_j(u)·γ(F_j u)(∂F_j u) du. Fix j and put Φ_j(z) := w_j(z)·ω(G_j z)(∂G_j z).
 (a) For u ∈ A_j, F_j(u) ∈ spt S by (vi), so by (ix) and Step 5 (at z = ι(t, u) ∈ B_j for t ∈ (0, 1); the interval integral over [0, 1] equals the integral over (0, 1)): g_j(u)·γ(F_j u)(∂F_j u) = ∫_0^1 g_j(u) t^k ω(tF_j u)(Fin.cons (F_j u) (∂F_j u)) dt = ∫_{(0,1)} Φ_j(ι(t, u)) dt.
 (b) Φ_j is integrable on B_j. It is measurable: w_j is measurable, G_j is continuous, z ↦ DG_j(z) is Borel (Mathlib measurable_fderiv), and (y, v) ↦ ω(y)(v) is continuous. For every z, ‖DG_j(z)‖ ≤ ρ + L_j (norm_fderiv_le_of_lipschitz and Step 3(b)), so |Φ_j(z)| ≤ |w_j(z)|·‖ω‖_∞·∏_{a=0}^{k} ‖DG_j(z)e_a‖ ≤ (ρ + L_j)^{k+1}‖ω‖_∞·|w_j(z)|, which is integrable on B_j by Step 3(c).
 (c) By Step 1 (Fubini) and (a): ∫_{B_j} Φ_j = ∫_{A_j} ∫_{(0,1)} Φ_j(ι(t, u)) dt du = I_j.
 Hence HasSum (j ↦ ∫_{B_j} w_j(z)·ω(G_j z)(∂G_j z) dz) (S(γ)) = HasSum (…) (R(ω)).

Steps 3(a)–(c), 7 and 8 give the conclusion. ∎

## Key steps

1. Coordinates z = ι(s, u) on ℝ^{n+2} ≅ ℝ × ℝ^{n+1} carry Lebesgue measure to the product measure: Tonelli/Fubini on cylinders (0,1) × A.
2. Bound F_j by the 1-Lipschitz radial retraction onto B̄_ρ ⊇ spt S without changing it near A_j; G_j(z) := σ(s(z))·F̂_j(τ(z)) is Lipschitz, B_j := (0,1) × A_j, w_j := g_j∘τ is integrable on B_j.
3. On B_j, G_j = s·F_j(τ) near z, so ∂G_j = (F_j(u), t∂F_j(u)) and ω(G_j)(∂G_j) = t^{n+1} ω(tF_j u)(F_j u, ∂F_j u).
4. Cone Jacobian: J(a, tw) = t^{n+1}J(a, w) ≤ t^{n+1}|a|J(w), so JG_j ≤ ρ JF_j and Σ∫|w_j|JG_j ≤ ρΣ∫|g_j|JF_j < ∞.
5. Since F_j(A_j) ⊆ spt S, the cone formula and S's representation give R(ω) = S(γ) = Σ_j ∫_{A_j} g_j ∫_0^1 t^{n+1}ω(tF_j)(F_j, ∂F_j) dt du = Σ_j ∫_{B_j} w_j ω(G_j)(∂G_j) by Fubini (integrability from the operator-norm bound).

## Reference use

### local-project

Queries:
- `sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `rg -n 'theorem exists_contDiff_support_eq_eq_one_iff|lemma measure_compl_support|theorem volume_preserving_piFinSuccAbove|theorem EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp|theorem norm_fderiv_le_of_lipschitz|theorem measurable_to_countable.|theorem enorm_integral_le_lintegral_enorm|theorem setIntegral_congr_set|theorem measurable_fderiv |def curryLeft|theorem extDeriv_apply|theorem hasFDerivAt_integral_of_dominated_of_fderiv_le..' local-references/123e8435b4a2469b/mathlib/Mathlib -g '*.lean'`
- `grep -rln 'contDiff_parametric|ContDiff.*intervalIntegral|contDiff_integral' mathlib/Mathlib (no match)`
- `python3 -I over dag.json (2375 nodes): keyword search homotop|cone|parametri|Lipschitz|Gram|orientation|approximate tangent|density|area formula|pushforward; status, candidate_commit and child/dependency closure of the reuse targets; byte equality of lean_statement with each handoff; replay of Runtime._existing_lean_name_problem for all 12 names`
- `git show <candidate>:GMT/Ch07/Submission.lean | grep -n 'theorem Submission.<name>|sorry' for the 8 reused candidates; cross-candidate comparison of 77 shared theorem headers`
- `lake env lean /tmp/cone-split-check/Final.lean (12 exact child types; parent assembly; Lean proofs of ecf_im_lipschitz_parametrization and ecf_isIntegerMultiplicity_of_parametrization from the reused types; Fin.cons, enorm and inner meaning checks; #print axioms)`
- `sed -n 441,551p and 850,866p book/chapter-06.txt`
- `grep -n '_existing_lean_name_problem|_accepted_checkpoint|def ensure|_overlay_accepted_children|cited_inherited|_reference_use_problem' /runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean/{runtime,store,inherited}.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Curry.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ParametricIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-existence-of-minimizing-filling-a1-cone-filling-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-vanish-off-support-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-9310c84433/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-imrep-mass-and-support-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-1df3e47686/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-im-calculus-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-im-series-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-53b6b2be95/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-covector-gram-bounds-a1/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean/store.py`
- `/runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean/inherited.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/cone-split-check/Final.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) Ch07 contract is byte-identical (sha256 e4148e7f…) to the workspace Contract.lean and Submission.lean.

Availability of the cited Mathlib facts:
- The pinned Mathlib contains every Mathlib fact the new children cite: exists_contDiff_support_eq_eq_one_iff, Measure.measure_compl_support, volume_preserving_piFinSuccAbove, EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp, ContinuousAlternatingMap.curryLeft, extDeriv_apply, measurable_to_countable', enorm_integral_le_lintegral_enorm, setIntegral_congr_set, measurable_fderiv, norm_fderiv_le_of_lipschitz and hasFDerivAt_integral_of_dominated_of_fderiv_le''.
- It has no C^∞ parametric-integral lemma (no match). B1 therefore reuses the accepted cmcdt_lpo_slice_param_integral.
- No cone construction, homotopy operator or general integrality-of-parametrization theorem exists in the snapshot project or in SimonGMT.

Reuse of DAG checkpoints:
- The DAG holds comparator-accepted checkpoints that are exactly E2–E4, E1/(MR), G2–G6 for one piece, the G4–G6 summation, (IMC), A2a and (VO). These are dor_lmb_fcd_imp_parametric_rep, dor_imrep_massOn_eq_measure_and_support, dimred_mbl_dt_lpip_lipschitz_piece_current, cmcdt_im_series, cmc_imRep_locality_restrict_sub, covectorEuclideanNorm_gram_bounds and dtc_vanish_off_support.
- Their frozen types match byte for byte. Their candidate commits contain the declared theorems, with the only sorry in main_theorem. Their closures are fully accepted, and the shared theorem headers are identical across candidates.
- The runtime permits identical-type reuse of accepted checkpoints across branches. The four new ecf_ names are unreserved.

Lean checks:
- All 12 child types elaborate.
- The parent assembly compiles.
- Both glue children are proved in Lean from the exact reused types, with 0 errors and only stub sorries.
