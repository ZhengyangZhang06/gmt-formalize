# Parent-supplied natural-language proof

- Parent DAG node: `root.existence_of_minimizing_filling-a1.cone_filling-a1.cone_parametrization-a1`
- Child DAG node: `root.existence_of_minimizing_filling-a1.cone_filling-a1.cone_parametrization-a1.piece_weight-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Steps 6 and 7 of the selected node's supplied proof (A4 and F5 of the cone-filling proof), specialized to one piece.
CF(b) denotes part (b) of the sibling cylinder_fubini (cmcdt_lpi_cyl_fubini with n := k and this A; its cylinder is Cyl(A)). GC(i) and GC(ii) denote the two parts of the sibling gram_cone. J(v) := √det[⟨v_i, v_j⟩] as there.

Proof.
1. (Measurability.) Let f(z) := ‖(g(τ z) : ℝ)‖ₑ·ofReal(JG(z)).
   τ is continuous and g is measurable, so z ↦ g(τ z) is measurable, and hence so is z ↦ ‖(g(τ z) : ℝ)‖ₑ.
   For each pair (a, b), z ↦ DG(z)e_a is measurable (measurable_fderiv_apply_const). The inner product is continuous (continuous_inner), so z ↦ ⟨DG(z)e_a, DG(z)e_b⟩ is measurable.
   The determinant of a (k+1)×(k+1) matrix is a finite sum over permutations of signed products of entries (Matrix.det_apply). So z ↦ det[⟨DG(z)e_a, DG(z)e_b⟩] is measurable (Finset.measurable_sum, Finset.measurable_prod).
   Composing with the continuous maps Real.sqrt and ENNReal.ofReal, z ↦ ofReal(JG(z)) is measurable. Hence f is measurable.
2. (Tonelli.) By CF(b), ∫⁻_{Cyl(A)} f = ∫⁻_{u∈A} ∫⁻_{t∈(0,1)} f(ι(t, u)) dt du.
3. (Pointwise bound.) Fix u ∈ A and t ∈ (0, 1). Then τ(ι(t, u)) = u (WithLp.ofLp_toLp, Fin.tail_cons, WithLp.toLp_ofLp).
   By hypothesis DG(ι(t, u))e_a = V_a for every a, where V := Fin.cons (F u) (t·∂F(u)). So the Gram matrix in JG(ι(t, u)) is (⟨V_a, V_b⟩)_{a,b}.
   Apply gram_cone with a := F(u) and w := ∂F(u), noting t ≥ 0:
   JG(ι(t, u)) = J(F u, t·∂F(u)) = t^k·J(F u, ∂F(u)) (GC(i)) ≤ t^k·‖F(u)‖·J(∂F(u)) (GC(ii), multiplied by t^k ≥ 0) ≤ ρ·JF(u).
   The last step uses 0 ≤ t^k ≤ 1 (as 0 < t < 1), 0 ≤ ‖F(u)‖ ≤ ρ, and J(∂F(u)) = JF(u) ≥ 0 (a square root).
   Since ρ ≥ ‖F(u)‖ ≥ 0, ofReal(ρ·JF(u)) = ofReal(ρ)·ofReal(JF(u)) (ENNReal.ofReal_mul).
   ENNReal.ofReal and multiplication in [0, ∞] are monotone, so f(ι(t, u)) ≤ ofReal(ρ)·(‖(g(u) : ℝ)‖ₑ·ofReal(JF(u))) =: c_u.
4. (Inner integral.) For u ∈ A, step 3 and monotonicity of the integral on the measurable set (0, 1) (setLIntegral_mono') give
   ∫⁻_{t∈(0,1)} f(ι(t, u)) dt ≤ ∫⁻_{(0,1)} c_u dt = c_u·λ((0,1)) = c_u (setLIntegral_const, Real.volume_Ioo).
5. (Outer integral.) Step 4 and monotonicity on the measurable set A (setLIntegral_mono') give
   ∫⁻_{u∈A} ∫⁻_{t∈(0,1)} f(ι(t, u)) dt du ≤ ∫⁻_A ofReal(ρ)·(‖(g(u) : ℝ)‖ₑ·ofReal(JF(u))) du = ofReal(ρ)·∫⁻_A ‖(g(u) : ℝ)‖ₑ·ofReal(JF(u)) du.
   The equality pulls out the finite constant ofReal(ρ) ≠ ∞ (lintegral_const_mul').
6. Steps 2 and 5 give the claim.
   If A = ∅, both sides are 0. The argument needs ρ ≥ 0 only at points u ∈ A, where it follows from ‖F(u)‖ ≤ ρ. ∎

Supplementary Lean fragment (not part of the numbered proof). The following measurability statement for step 1 was checked with lake env lean after import GMT.Ch07.Submission, inside namespace GMT.Ch07 with the contract's opens:
example (k P : ℕ) (G : Euclid (k+1) → Euclid P) :
    Measurable (fun z => ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun a b : Fin (k + 1) => inner ℝ (fderiv ℝ G z (EuclideanSpace.single a 1)) (fderiv ℝ G z (EuclideanSpace.single b 1)))))) := by
  have hm : ∀ a b : Fin (k+1), Measurable (fun z => inner ℝ (fderiv ℝ G z (EuclideanSpace.single a 1)) (fderiv ℝ G z (EuclideanSpace.single b 1))) :=
    fun a b => continuous_inner.measurable.comp ((measurable_fderiv_apply_const ℝ G (EuclideanSpace.single a 1)).prodMk (measurable_fderiv_apply_const ℝ G (EuclideanSpace.single b 1)))
  have hdet : Measurable (fun z => Matrix.det (Matrix.of fun a b : Fin (k + 1) => inner ℝ (fderiv ℝ G z (EuclideanSpace.single a 1)) (fderiv ℝ G z (EuclideanSpace.single b 1)))) := by
    simp only [Matrix.det_apply]
    refine Finset.measurable_sum _ (fun σ _ => ?_)
    refine Measurable.const_smul ?_ _
    exact Finset.measurable_prod _ (fun i _ => by simpa using hm (σ i) i)
  exact ENNReal.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp hdet)

## Key steps

1. f(z) = |g(τz)|·JG(z) is measurable: fderiv is Borel and the Gram determinant is a polynomial in the entries.
2. Tonelli on the cylinder (cylinder_fubini (b)) gives ∫⁻_{Cyl A} f = ∫⁻_A ∫⁻_{(0,1)} f(ι(t,u)) dt du.
3. For u ∈ A and t ∈ (0,1), gram_cone gives JG(ι(t,u)) = J(F u, t∂F u) = t^k J(F u, ∂F u) ≤ t^k‖F u‖JF(u) ≤ ρ·JF(u).
4. Integrate the pointwise bound over (0,1), which has measure 1, and then over A, pulling out the constant ofReal ρ.

## Reference use

### local-project

Queries:
- `sha256sum local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean`
- `rg -n 'theorem measurable_fderiv |theorem norm_fderiv_le_of_lipschitz|theorem bounded_above_of_compact_support|theorem map_smul_univ|theorem volume_preserving_piFinSuccAbove|theorem EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp|theorem integral_Ioc_eq_integral_Ioo|theorem integral_of_le' local-references/123e8435b4a2469b/mathlib/Mathlib -g '*.lean'`
- `rg -n 'closedBall.*LipschitzWith 1|LipschitzWith 1.*closedBall|radialRetraction|retractionBall|ball_retraction|lipschitzWith_one_norm_smul' mathlib/Mathlib (no match); rg -n LipschitzWith mathlib/Mathlib/Analysis/InnerProductSpace`
- `rg -n 'ContinuousEval' mathlib/Mathlib/Analysis/Normed/Module/Multilinear mathlib/Mathlib/Analysis/Normed/Module/Alternating mathlib/Mathlib/Topology/Algebra/Module/Alternating mathlib/Mathlib/Topology/Algebra/Module/Multilinear`
- `python3 -I over dag.json: lean_name/lean_statement search for cyl|fubini, Matrix.det with inner ℝ (Gram lemmas), LipschitzWith 1, Fin.cons with Matrix.det; status and candidate of cmcdt_lpi_cyl_fubini; uniqueness grep of ecf_cp_ball_retraction, ecf_cp_gram_cone, ecf_cp_cone_map, ecf_cp_piece_integral, ecf_cp_piece_weight in dag.json, nodes/, GMT, simongmt`
- `git show 8597f3f04cb72a70e4b11d91699ec1f9f45dfc0f:GMT/Ch07/Submission.lean | grep -n 'theorem Submission.cmcdt_lpi_cyl_fubini|sorry'`
- `lake env lean /tmp/cone-param-split/Final.lean (six child types generated from this JSON plus the parent assembly and #print axioms); lake env lean /tmp/cone-param-split/{Meaning,Names,Spot}.lean`
- `sed -n 520,555p and 850,870p book/chapter-06.txt`
- `grep -n '_existing_lean_name_problem|_accepted_checkpoint' /runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean/runtime.py`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/FDeriv/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Pi.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Multilinear/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-existence-of-minimizing-filling-a1-cone-filling-a1-cone-parametrization-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-existence-of-minimizing-filling-a1-cone-filling-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-existence-of-minimizing-filling-a1-cone-filling-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-lip-36d21f0b90/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-cf346c63e6ef/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/tmp/cone-param-split/Final.lean`
- `/tmp/cone-param-split/Split1.lean`
- `/tmp/cone-param-split/Meaning.lean`
- `/tmp/cone-param-split/Names.lean`
- `/tmp/cone-param-split/Spot.lean`

Snapshot and contract:
- The snapshot (project b4d606d, Mathlib 25730c7c) Ch07 Contract.lean is byte-identical (sha256 e4148e7f…) to the workspace Contract.lean and Submission.lean.

Mathlib facts the child proofs cite:
- All are present in the pinned Mathlib: measurable_fderiv, measurable_fderiv_apply_const, norm_fderiv_le_of_lipschitz, HasFDerivAt.smul, Filter.EventuallyEq.fderiv_eq, ContinuousAlternatingMap.map_smul_univ, ContinuousAlternatingMap.le_opNorm, ContinuousAlternatingMap.instContinuousEval, HasCompactSupport.exists_bound_of_continuous, Integrable.mono', setIntegral_congr_fun, intervalIntegral.integral_of_le, integral_Ioc_eq_integral_Ioo, setLIntegral_mono', lintegral_const_mul', Real.volume_Ioo, ENNReal.ofReal_mul, Submodule.starProjection, Submodule.sub_starProjection_mem_orthogonal, Submodule.mem_span_range_iff_exists_fun, Matrix.det_succ_row_zero, Matrix.det_mul, Matrix.det_of_isLowerTriangular, Real.sqrt_mul, Real.sqrt_sq, LipschitzWith.of_dist_le_mul and LipschitzWith.comp/max_const/min_const.
- Measurable.inner is not available; the proofs use continuous_inner instead.
- measurable_pi_lambda is deprecated; the proofs use measurable_pi_iff.

What is new and what is reused:
- No radial-retraction lemma exists in Mathlib or the DAG; the only LipschitzWith 1 projections are onto subspaces. This justifies ball_retraction.
- No DAG node states the cone Gram bound J(a, w) ≤ ‖a‖J(w) or the scaling J(a, tw) = t^k J(a, w). This justifies gram_cone.
- cmcdt_lpi_cyl_fubini is accepted at an identical type. Candidate 8597f3f0 declares it, and that commit's only sorry is main_theorem. It is reused.
- The five new ecf_cp_ names are unused everywhere.

Lean checks:
- All six child types elaborate.
- The exact parent type is proved from them with 0 errors.
- The axioms are standard, plus sorryAx from the stubs only.
- The meaning checks and spot checks pass.
