# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1`
- Child DAG node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.boundary_cone_transfer-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Notation. p := L.starProjection and q := Lᗮ.starProjection = I − p. H^k := μHE[k]. Λ^k := Covector (Euclid P) k. For a test k-form γ and t ∈ ℝ^P, γ(t + ·) denotes y ↦ γ(t + y).
No sibling children are used; every fact used is in scope after `import GMT.Ch07.Submission`. This includes Mathlib MultilinearMap.alternatization, ContDiffBump, euclideanHausdorffMeasure_smul₀ and euclideanHausdorffMeasure_homothety_image, and SimonGMT exteriorDerivative_apply and HasApproximateTangentSpaceAt.
0. (Fixing ♭: interior product with the frame.) Let h := (Nat.add_sub_of_le hd.le).symm : n = d + m and e := Fin.cast h. For v : Fin m → ℝ^P put u(v) := Fin.append f v ∘ e, the tuple (f_1, …, f_d, v_1, …, v_m).
 - Updating v_j updates exactly one entry of u(v): Fin.append f (update v j w) = update (Fin.append f v) (Fin.natAdd d j) w, checked pointwise with Fin.addCases.
 - So, for α ∈ Λ^n, v ↦ α(u(v)) is multilinear. It is alternating, because equal entries v_i = v_j (i ≠ j) give equal entries of u(v) at distinct indices.
 - It is bounded by ‖α‖∏_j|v_j| (le_opNorm; f is orthonormal).
 - Hence ♭α := (v ↦ α(u v)) ∈ Λ^m, and α ↦ ♭α is linear with ‖♭α‖ ≤ ‖α‖. So ♭ : Λ^n →L[ℝ] Λ^m is continuous linear (LinearMap.mkContinuous), with (♭α)(v) = α(Fin.append f v ∘ Fin.cast h).
 Applying the hypothesis to this ♭ gives, for every test n-form ω:
 (PF) S(ω) = ∫_L S₀(♭ω(t + ·)) dt, where ♭ω(t + ·) := y ↦ ♭(ω(t + y)) is a test m-form, so currentEval equals S₀ applied to it.
1. (S₀ only sees L^⊥.) Claim: let γ, γ' be test m-forms with γ(y)(w) = γ'(y)(w) for all y ∈ L^⊥ and all w ∈ (L^⊥)^m. Then S₀(γ) = S₀(γ').
 Proof.
 - Since θ₀ ≥ 1 on M₀, H^m(M₀ ∖ L^⊥) ≤ μ₀(ℝ^P ∖ L^⊥) = 0.
 - Take H^m-a.e. y ∈ M₀ such that y ∈ L^⊥ and ζ₀(y) is a unit orientation of a subspace Q_y with HasApproximateTangentSpaceAt m M₀ y Q_y (R₀.orients). Then Q_y ⊆ L^⊥, by the following lemma.
 (Tangent lemma.) If H^m(M₀ ∖ V) = 0 for a linear subspace V, y ∈ V and HasApproximateTangentSpaceAt m M₀ y Q, then Q ⊆ V.
 Proof:
  - Suppose z ∈ Q ∖ V. Then ρ := dist(z, V)/2 > 0, since V is closed, and m = finrank Q ≥ 1.
  - Let φ(x) := max(0, 1 − |x − z|/ρ). It is continuous with compact support, 0 ≤ φ ≤ 1, φ ≥ 1/2 on B(z, ρ/2), and φ = 0 on V.
  - For r > 0, η := η_{y,r} (x ↦ r⁻¹(x − y)) maps V onto V, so η(M₀) ∖ V = η(M₀ ∖ V). This set has H^m-measure r^{−m}H^m(M₀ ∖ V) = 0 (homothety scaling and translation invariance of μHE[m]).
  - Hence 0 ≤ ∫_{η(M₀)} φ dH^m ≤ H^m(η(M₀) ∩ B(z, ρ)) ≤ H^m(η(M₀) ∖ V) = 0 for every r > 0, so the tangent limit gives ∫_Q φ dH^m = 0.
  - But H^m⌞Q is m-dimensional Lebesgue measure on Q (isometry invariance and EuclideanSpace.euclideanHausdorffMeasure_eq_volume). So ∫_Q φ dH^m ≥ (1/2)H^m(Q ∩ B(z, ρ/2)) > 0, a contradiction.
  Apply the lemma with V = L^⊥.
 - Then ζ₀(y)(γ(y)) = ±γ(y)(τ) for an orthonormal basis τ of Q_y ⊆ L^⊥, so it equals ±γ'(y)(τ) = ζ₀(y)(γ'(y)).
 - The integrands of R₀.action(γ) and R₀.action(γ') agree a.e., so S₀(γ) = S₀(γ').
2. (Lifts and test forms.) For k ∈ {m − 1, m} let lift_k : Λ^k → Λ^{d+k} be the continuous linear map
 (lift_k β)(v_1, …, v_{d+k}) := (1/k!) Σ_{σ∈S_{d+k}} sgn(σ) ∏_{a=1}^d ⟨f_a, v_{σ(a)}⟩ · β(q v_{σ(d+1)}, …, q v_{σ(d+k)})
 (Mathlib MultilinearMap.alternatization; multilinear in v, hence continuous). Its two properties:
 (L1) (lift_k β)(f_1, …, f_d, w_1, …, w_k) = β(w_1, …, w_k) for w_j ∈ L^⊥. A term is nonzero only if v_{σ(a)} = f_a for all a ≤ d, since ⟨f_a, w_j⟩ = 0 and ⟨f_a, f_b⟩ = δ_ab. The rest is Σ_{π∈S_k} sgn(π)β(w_π) = k!β(w).
 (L2) (lift_k β)(v) = 0 if v consists of d − 1 vectors from {f_1, …, f_d} and k + 1 vectors from L^⊥. Each term contains a factor ⟨f_a, u⟩ with u ∈ L^⊥, or a mismatched ⟨f_a, f_b⟩ = 0.
 The bump ϕ. Fix ϕ ∈ C_c^∞(ℝ^P) with ϕ ≥ 0 and ϕ(0) > 0 (a ContDiffBump at 0). Then c_ϕ := ∫_L ϕ dH^d > 0, since ϕ > 0 on a relatively open neighbourhood of 0 in L and H^d⌞L is Lebesgue measure on L.
 The forms Ω_β. For a test k-form β put Ω_β(x) := ϕ(p x)·lift_k(β(q x)). This is a test (d + k)-form: it is C^∞, and tsupport Ω_β ⊆ {x : p x ∈ tsupport ϕ ∩ L, q x ∈ tsupport β}, which is compact since x = p x + q x.
 Evaluation: by (L1), for t ∈ L, y ∈ L^⊥ and w ∈ (L^⊥)^k,
 (E) ♭(Ω_β(t + y))(w) = Ω_β(t + y)(f, w) = ϕ(t)·β(y)(w),
 since p(t + y) = t and q(t + y) = y.
3. (∂S = 0 ⇒ ∂S₀ = 0.) Assume BoundaryVanishes S. Since n ≥ 2, this means S(dγ) = 0 for all test (n−1)-forms γ. As m ≥ 1, it suffices to show S₀(dβ) = 0 for every test (m−1)-form β.
 Let β be a test (m−1)-form and γ := Ω_β (k = m − 1), a test (n−1)-form. We compute ♭(dγ(x)) on w ∈ (L^⊥)^m, using dγ(x)(v_0, …, v_{n−1}) = Σ_i (−1)^i Dγ(x)[v_i](v_0, …, v̂_i, …, v_{n−1}) (SimonGMT exteriorDerivative_apply) with v = (f_1, …, f_d, w_1, …, w_m):
 - Terms v_i = f_a. Dγ(x)[f_a] = (Dϕ(px)[f_a])·lift(β(qx)) + ϕ(px)·lift(Dβ(qx)[q f_a]), and q f_a = 0. Evaluated on (f_1, …, f̂_a, …, f_d, w), the first part vanishes by (L2), and the second is 0.
 - Terms v_i = w_j, i = d + j − 1. Dγ(x)[w_j] = ϕ(px)·lift(Dβ(qx)[w_j]), because Dϕ(px)[p w_j] = 0. By (L1), its value on (f, ŵ_j) is ϕ(px)·Dβ(qx)[w_j](ŵ_j).
 Hence ♭(dγ(x))(w) = (−1)^d ϕ(px) Σ_j (−1)^{j−1} Dβ(qx)[w_j](ŵ_j) = (−1)^d ϕ(px)·dβ(qx)(w).
 For x = t + y with t ∈ L and y ∈ L^⊥ this reads ♭(dγ(t + y))(w) = (−1)^d ϕ(t)·dβ(y)(w). By step 1, applied to the test m-forms ♭dγ(t + ·) and (−1)^d ϕ(t)dβ, S₀(♭dγ(t + ·)) = (−1)^d ϕ(t) S₀(dβ).
 By (PF) with ω := dγ: 0 = S(dγ) = ∫_L (−1)^d ϕ(t) S₀(dβ) dt = (−1)^d c_ϕ S₀(dβ). So S₀(dβ) = 0 for all β, i.e. S₀.boundary = 0, which is BoundaryVanishes S₀ (degree m ≥ 1).
4. (Cone transfer.) Assume IsConeCurrent S and fix λ > 0. For a test k-form γ write η^#γ(x) := λ^{−k}γ(λ^{−1}x). This is the affine pull-back by dilation 0 λ (x ↦ λ^{−1}x) used in blowUp, by multilinearity. Since dilation 0 λ '' univ = univ, currentEval (blowUp T 0 λ) γ = T(η^#γ) for T ∈ {S, S₀}.
 (a) η^# preserves "agreement on L^⊥". If γ, γ' agree on L^⊥ × (L^⊥)^m as in step 1, so do η^#γ and η^#γ', because λ^{−1}y ∈ L^⊥ for y ∈ L^⊥. Hence η_#S₀(γ) := S₀(η^#γ) also depends only on the restriction of γ to L^⊥ × (L^⊥)^m.
 (b) Scaling of slices. Let ω be a test n-form and β_s := ♭ω(s + ·). Then
 ♭((η^#ω)(t + y)) = λ^{−n}♭(ω(λ^{−1}t + λ^{−1}y)) = λ^{−d}·(η^#β_{λ^{−1}t})(y),
 since λ^{−n} = λ^{−d}λ^{−m}. By (PF) and the cone hypothesis,
 S(ω) = S(η^#ω) = ∫_L λ^{−d} S₀(η^#β_{λ^{−1}t}) dH^d(t) = ∫_L η_#S₀(β_s) dH^d(s).
 The last step is the change of variables t = λs on L: μHE[d](λA) = λ^d μHE[d](A) (Mathlib euclideanHausdorffMeasure_smul₀ or euclideanHausdorffMeasure_homothety_image), and L is invariant under scaling. Also S(ω) = ∫_L S₀(β_s) ds by (PF). Therefore:
 (∗) ∫_L S₀(β_s) ds = ∫_L η_#S₀(β_s) ds for every test n-form ω.
 (c) Testing. Let β be a test m-form and ω := Ω_β (k = m). By (E), β_s(y)(w) = ϕ(s)β(y)(w) for y ∈ L^⊥ and w ∈ (L^⊥)^m. By step 1, S₀(β_s) = ϕ(s)S₀(β); by (a), η_#S₀(β_s) = ϕ(s)η_#S₀(β). Then (∗) gives c_ϕ S₀(β) = c_ϕ η_#S₀(β), so S₀(β) = S₀(η^#β) = currentEval (blowUp S₀ 0 λ) β.
 As λ > 0 and β were arbitrary, IsConeCurrent S₀. ∎

## Key steps

1. Construct the interior product ♭ with the frame f. Approximate tangent planes of a set lying in L^⊥ up to a null set are contained in L^⊥. Hence S₀ only sees the values of a test form at points of L^⊥ on (n−d)-tuples from L^⊥.
2. Forms Ω_β = ϕ(p x)·lift(β(q x)) = ϕ(p x)·dt^1∧⋯∧dt^d∧q^#β satisfy ♭Ω_β(t + y) = ϕ(t)β(y) on L^⊥.
3. Direct evaluation of d gives ♭(dΩ_β)(t + y) = (−1)^d ϕ(t) dβ(y) on L^⊥, so S(dΩ_β) = 0 forces S₀(dβ) = 0.
4. Dilations scale slices: ♭(η^#ω)(t + ·) = λ^{−d}η^#(♭ω(λ^{−1}t + ·)); a change of variables on L and testing with Ω_β give S₀(β) = S₀(η^#β).

## Reference use

### local-project

Queries:
- `cat local-references/123e8435b4a2469b/manifest.json; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD (b4d606d, 25730c7c, 2b36630: pins match)`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical; sha256 e4148e7f…)`
- `grep -n -E '^(theorem|def|structure|abbrev|instance)' over SimonGMT Chapter06/{Currents,Mass,CurrentLocalEquality,AffineCurrentPushforward,Forms}.lean; head of Chapter06/{Product,WedgeForms,GeometricPointProduct,Representation}.lean`
- `sed -n 1,140p SimonGMT Chapter03/Rectifiable.lean (CountablyRectifiable, HasApproximateTangentSpaceAt, blowUpMap); ls Chapter02 (AreaFormula, AreaLipschitz, CoareaLinear, CoareaProjection)`
- `grep -n -E 'theorem|def ' local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (euclideanHausdorffMeasure_zero, Submodule.measurePreserving_measurableEquivProd, AffineSubspace.euclideanHausdorffMeasure_eq_lintegral, euclideanHausdorffMeasure_homothety_image)`
- `lake env lean /tmp/sos-decomp/Probe.lean and Probe2.lean: #check after import GMT.Ch07.Submission (in scope: ContinuousAlternatingMap.curryLeft, MultilinearMap.alternatization, ContDiffBump, lintegral_prod, MeasurableSpace.induction_on_inter, LipschitzWith.ae_differentiableAt, LipschitzOnWith.extend_real, MeasurableSet.image_of_continuousOn_injOn, exists_partition_approximatesLinearOn_of_hasFDerivWithinAt, Besicovitch.ae_tendsto_measure_inter_div, Besicovitch.ae_tendsto_rnDeriv, VitaliFamily.ae_tendsto_average_norm_sub, exteriorDerivative_apply, CurrentOn.boundary_boundary; not in scope: covectorWedge, GeometricCurrentOn.pointProduct, Add/Neg/SMul on GeometricCurrentOn, SimonGMT AreaLipschitz lemmas, kernel API)`
- `python3 over dag.json: cone_splitting-a1 siblings and statuses; accepted IMRep lemmas (dtc_imrep_current, imrep_weighted_orient_indicator_ae_eq, imrep_measure_eq_of_represents_same_current, imrep_represents_massOn_eq_measure, imrep_carrier_sdiff_support_null, rsd_isIntegerMultiplicity_int_combination, dtc_blowUp_imrep, dtc_vanish_off_support); emf_exists_cone_filling (decomposing, no support conclusion); dpf_ bi-Lipschitz pieces (not accepted); occurrences of dimred_cs_sos in dag.json: 0`
- `git show dd88db7, 9203aee, 77fcc7d: GMT/Ch07/Submission.lean (listed dependencies are merged into a child's Submission; the accepted parent dtc_isIntegerMultiplicity_sub adds a SimonGMT import)`
- `read nodes/root-dimension-reduction-results-a1-cone-splitting-a1/{parent-supplied-natural-proof.md,decomposition-v1.json} (reuse precedent), nodes/root-existence-of-minimizing-filling-a1-cone-filling-a1/parent-supplied-natural-proof.md (cone construction adapted for cone_filling_subspace), and the handoffs of the 6 reused accepted nodes`
- `lake env lean /tmp/sos-decomp/CheckFinal.lean (12 child types as Submission stubs, assembly of dimred_cs_split_off_spine including the finrank L = 0 case, #print axioms) and Check5.lean (cone_filling_subspace instantiated at degree n − finrank L)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/AffineCurrentPushforward.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Product.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/WedgeForms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaProjection.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-existence-of-minimizing-filling-a1-cone-filling-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-localize-a1-imrep-current-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-imrep-measure-unique-a1-vect-8c0391929c/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-imrep-measure-unique-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-mass-equals-measure-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-support-null-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-integer-combination-a1/parent-child-handoff.json`
- `/tmp/sos-decomp/CheckFinal.lean`

Pins match. The snapshot is at project b4d606d (= workspace HEAD) with mathlib 25730c7c and SimonGMT 2b36630, and the snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

What the library lacks. SimonGMT has none of:
- slicing;
- Cartesian products of currents beyond point products;
- a Lipschitz push-forward;
- a coarea formula on rectifiable sets (only the linear one).
WedgeForms, the area formula (Chapter02.AreaLipschitz) and Mathlib's kernel API are outside the contract import closure. GeometricCurrentOn has only Sub and Zero instances.
Consequences for the split:
- no child type mentions products or wedges;
- the product structure is passed as an action identity over a quantified interior product ♭ (Fin.append f v ∘ Fin.cast), plus the measure identity and concentration on L^⊥;
- the area-formula import is assigned to the lipschitz_tangent subtree, from which dependents inherit it (precedent: accepted dtc_isIntegerMultiplicity_sub added a SimonGMT import; leaves cannot add imports).
Mathlib facts the proofs use are all in scope, including the μHE Fubini lemmas Submodule.measurePreserving_measurableEquivProd and AffineSubspace.euclideanHausdorffMeasure_eq_lintegral.

Reuse. The parent dependency im_mass_measure, cited by the supplied proof, is not accepted. Six comparator-accepted declarations are reused in its place, with byte-identical types and commits present: dtc_imrep_current 642d745, imrep_weighted_orient_indicator_ae_eq 2d0f5bb, imrep_measure_eq_of_represents_same_current 6907c2c, imrep_represents_massOn_eq_measure c004e5e, imrep_carrier_sdiff_support_null d15b5cf, rsd_isIntegerMultiplicity_int_combination 568bfe5. Listed dependencies are merged into a child's Submission.lean (checked on accepted commits).

No reuse:
- emf_exists_cone_filling is not accepted and lacks the support conclusion, so cone_filling_subspace is new; the construction is adapted from that node's proof.
- The dpf_ bi-Lipschitz/tangent lemmas are not accepted, so lipschitz_tangent is new.

Lean check. All 12 child types elaborate, and the frozen parent type is proved from them, including the finrank L = 0 case. Axioms are propext, sorryAx (stubs only), Classical.choice and Quot.sound. The 6 new dimred_cs_sos_ names are unused elsewhere.
