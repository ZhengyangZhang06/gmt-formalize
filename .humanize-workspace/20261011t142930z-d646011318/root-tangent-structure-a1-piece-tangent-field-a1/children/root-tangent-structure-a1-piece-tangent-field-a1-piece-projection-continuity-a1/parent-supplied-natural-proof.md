# Parent-supplied natural-language proof

- Parent DAG node: `root.tangent_structure-a1.piece_tangent_field-a1`
- Child DAG node: `root.tangent_structure-a1.piece_tangent_field-a1.piece_projection_continuity-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the parent proof (node root.tangent_structure-a1.piece_tangent_field-a1), step 3 (continuity on each piece), specialized to a single piece. The parent's steps 1–2 enter through the sibling lemma ts_starProjection_range_continuousOn_injective (key projection_continuity), so G is written directly as Π ∘ DF ∘ ψ and no adjoint is needed. Compactness of C and the Lipschitz bound on F are not used in this step and are not assumed. No errata apply.

Conventions. X := ℝⁿ = EuclideanSpace ℝ (Fin n) (nonempty, since 0 ∈ X); E := Ambient n ℓ; L(V, W) := V →L[ℝ] W with the operator-norm topology; DF(w) := fderiv ℝ F w ∈ L(X, E). For A ∈ L(X, E), Π(A) := (LinearMap.range A.toLinearMap).starProjection ∈ L(E, E), and S := {A ∈ L(X, E) : A injective}.
Hypotheses: (H1) c > 0 and c|v − w| ≤ |F(v) − F(w)| for all v, w ∈ C; (H2) DF(w) ∈ S for every w ∈ C; (H3) DF is continuous on C.
Sibling lemma used (projection_continuity, Lean name ts_starProjection_range_continuousOn_injective): for all n, ℓ, Π is continuous on S.

Proof.
1. F is injective on C. Let v, w ∈ C with F(v) = F(w). By (H1), c|v − w| ≤ |F(v) − F(w)| = 0. If |v − w| > 0, then c|v − w| > 0 because c > 0, a contradiction. So |v − w| ≤ 0, i.e. v = w.
2. The inverse map. Let ψ := Function.invFunOn F C : E → X (this needs only Nonempty X). For every y ∈ F(C), i.e. y = F(w₀) for some w₀ ∈ C, we have ψ(y) ∈ C and F(ψ(y)) = y (Function.invFunOn_mem, Function.invFunOn_eq). For w ∈ C, ψ(F(w)) ∈ C and F(ψ(F(w))) = F(w), so ψ(F(w)) = w by step 1 (Set.InjOn.leftInvOn_invFunOn). In particular ψ maps F(C) into C.
3. ψ is continuous on F(C). Let y, y' ∈ F(C). Apply (H1) to ψ(y), ψ(y') ∈ C and use F(ψ(y)) = y, F(ψ(y')) = y' (step 2): c|ψ(y) − ψ(y')| ≤ |y − y'|, i.e. |ψ(y) − ψ(y')| ≤ c⁻¹|y − y'|. Thus ψ is Lipschitz on F(C) with constant c⁻¹ ≥ 0 (LipschitzOnWith.of_dist_le_mul), hence continuous on F(C) (LipschitzOnWith.continuousOn).
4. Definition of G and its continuity. Define G : E → L(E, E) by G(y) := Π(DF(ψ(y))). On F(C), three facts combine:
   - ψ is continuous on F(C) and maps F(C) into C (steps 2–3);
   - DF is continuous on C (H3) and maps C into S (H2);
   - Π is continuous on S (sibling lemma).
   Composing continuous-on maps along these inclusions (ContinuousOn.comp, twice) shows that y ↦ Π(DF(ψ(y))) = G(y) is continuous on F(C).
5. Values. For w ∈ C, ψ(F(w)) = w by step 2, hence G(F(w)) = Π(DF(w)) = (LinearMap.range (fderiv ℝ F w).toLinearMap).starProjection.
By steps 4 and 5, G has both required properties. ∎

Appendix (implementation aid, not part of the argument). The following Lean proof of exactly the frozen type was checked to compile, with axioms propext, Classical.choice and Quot.sound only, when inserted as a single theorem before `main_theorem` in an otherwise unchanged copy of the frozen GMT/Ch04/Submission.lean (no import added; the controller's leaf delta check accepts it):

theorem Submission.ts_piece_projection_continuousOn_image : (∀ (n ℓ : ℕ) (C : Set (EuclideanSpace ℝ (Fin n))) (F : EuclideanSpace ℝ (Fin n) → Ambient n ℓ) (c : ℝ), 0 < c → (∀ v ∈ C, ∀ w ∈ C, c * ‖v - w‖ ≤ ‖F v - F w‖) → (∀ w ∈ C, Function.Injective (fderiv ℝ F w)) → ContinuousOn (fderiv ℝ F) C → ∃ G : Ambient n ℓ → (Ambient n ℓ →L[ℝ] Ambient n ℓ), ContinuousOn G (F '' C) ∧ ∀ w ∈ C, G (F w) = (LinearMap.range (fderiv ℝ F w).toLinearMap).starProjection) := by
  intro n ℓ C F c hc hlow hinj hcont
  classical
  -- F is injective on C
  have hInjOn : Set.InjOn F C := by
    intro v hv w hw hvw
    have h := hlow v hv w hw
    rw [hvw, sub_self, norm_zero] at h
    have h' : ‖v - w‖ ≤ 0 := by
      by_contra hpos
      exact absurd h (not_le.mpr (mul_pos hc (lt_of_not_ge hpos)))
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h')
  -- the inverse ψ of F on C
  set ψ : Ambient n ℓ → EuclideanSpace ℝ (Fin n) := Function.invFunOn F C with hψ
  have hψmaps : Set.MapsTo ψ (F '' C) C := fun y hy ↦ Function.invFunOn_mem hy
  have hFψ : ∀ y ∈ F '' C, F (ψ y) = y := fun y hy ↦ Function.invFunOn_eq hy
  have hψF : ∀ w ∈ C, ψ (F w) = w := fun w hw ↦ hInjOn.leftInvOn_invFunOn hw
  -- ψ is Lipschitz (constant c⁻¹) on F '' C
  have hψcont : ContinuousOn ψ (F '' C) := by
    refine (LipschitzOnWith.of_dist_le_mul (K := Real.toNNReal c⁻¹) fun y hy y' hy' ↦ ?_).continuousOn
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (inv_nonneg.mpr hc.le)]
    have h := hlow (ψ y) (hψmaps hy) (ψ y') (hψmaps hy')
    rw [hFψ y hy, hFψ y' hy'] at h
    rw [inv_mul_eq_div, le_div_iff₀ hc, mul_comm]
    exact h
  refine ⟨fun y ↦ (LinearMap.range (fderiv ℝ F (ψ y)).toLinearMap).starProjection, ?_, ?_⟩
  · exact (Submission.ts_starProjection_range_continuousOn_injective n ℓ).comp
      (hcont.comp hψcont hψmaps) (fun y hy ↦ hinj (ψ y) (hψmaps hy))
  · intro w hw
    simp only [hψF w hw]

## Key steps

1. The lower bound c|v − w| ≤ |F v − F w| with c > 0 makes F injective on C
2. ψ := Function.invFunOn F C maps F(C) into C, satisfies ψ(F w) = w on C, and is c⁻¹-Lipschitz, hence continuous, on F(C)
3. G := Π ∘ DF ∘ ψ is continuous on F(C) by composing ψ, DF (continuous on C with injective values) and Π (continuous on injective maps, sibling lemma)
4. G(F w) = Π(DF w) for w ∈ C because ψ(F w) = w

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-piece-tangent-field-a1/{parent-child-handoff.json,parent-supplied-plan.md,parent-supplied-natural-proof.md}`
- `sha256sum GMT/Ch04/Contract.lean GMT/Ch04/Submission.lean <snapshot>/project/GMT/Ch04/Contract.lean`
- `git diff ff75f52 2cce809724fc09db16dc21873e5f9cd1ee6e2dfa -- GMT/ lakefile.toml lake-manifest.json GMT.lean`
- `rg -n "theorem inverse_continuousAt|theorem eq_starProjection_of_mem_of_inner_eq_zero|theorem continuousOn_iff'|theorem _root_.Measurable.stronglyMeasurable|theorem Measurable.find|theorem measurable_find |theorem ContinuousOn.measurable_piecewise|theorem adjoint_inner_left|def adjoint " <snapshot>/mathlib/Mathlib`
- `rg -n "isOpen_setOf_injective|isOpen_injective|starProjection.*[Cc]ontinu|[Cc]ontinu.*starProjection" <snapshot>/mathlib/Mathlib`
- `rg -n "theorem .*isUnit_iff|isUnit_toLinearMap|injective_iff_surjective|theorem mul_inverse_cancel|clm_comp|instMeasurableSpace|instBorelSpace|invFunOn_mem|invFunOn_eq|leftInvOn_invFunOn|of_dist_le_mul|FiniteDimensional.proper" <snapshot>/mathlib/Mathlib`
- `rg -n "starProjection|orthogonalProjection" .lake/packages/simongmt/Poincare/SimonGMT | rg -i "contin|measurab"; rg -n "Measurable.find|measurable_piecewise|Nat.find" .lake/packages/simongmt/Poincare/SimonGMT`
- `lake env lean GMT/Ch04/Submission.lean -o /tmp/ch04-ptf-decomp/olean/GMT/Ch04/Submission.olean`
- `LEAN_PATH=$(lake env printenv LEAN_PATH):/tmp/ch04-ptf-decomp/olean lean /tmp/ch04-ptf-decomp/Avail.lean Avail2.lean Avail3.lean (#check under the frozen imports only)`
- `python3 -I /tmp/ch04-ptf-decomp/scripts/gen.py children.json gen (verifier gmt-compare.child_modules + lean_contract.validate_lean_statement); lean gen/Challenge_*.lean`
- `lean /tmp/ch04-ptf-decomp/Synth_frozen.lean /tmp/ch04-ptf-decomp/Synth_imports.lean (#synth instance comparison)`
- `lean /tmp/ch04-ptf-decomp/Assembly.lean (parent frozen type from sorry'd children)`
- `lean /tmp/ch04-ptf-decomp/Frozen1.lean; lean /tmp/ch04-ptf-decomp/Frozen23.lean (complete proofs, frozen imports only, #print axioms)`
- `python3 -I /tmp/ch04-ptf-decomp/scripts/sim.py (controller leaf_verification.check_source_delta on each single-theorem insertion)`
- `lean GMT/Ch04/Submission.lean -o /tmp/ch04-ptf-decomp/sim2-olean/GMT/Ch04/Submission.olean (cwd simroot2); lean /tmp/ch04-ptf-decomp/gen-sim/SolAx_*.lean (comparator-style NodeSolution + #print axioms)`
- `grep -c <name> dag.json; grep -rl <name> nodes/; git grep -l <names> over every ref from git for-each-ref`
- `git show <ref>:GMT/Ch04/Submission.lean | grep '^import' over every ref (import-change scan)`
- `python3 survey of nodes/*/decomposition-v*.json should_split decisions; grep decomposition nodes/*/rlcr-plan-v1.md`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/project/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/GMT/Ch04/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-piece-tangent-field-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-piece-tangent-field-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-tangent-structure-a1-piece-tangent-field-a1/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-lipschitz-pieces-a1-lusin-exhaustion-a1/rlcr-plan-v1.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-lipschitz-pieces-a1-lusin-exhaustion-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-6e6a457c9391/_recursive_lean/leaf_verification.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Normed/Ring/Units.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Normed/Operator/Banach.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Algebra/GroupWithZero/Units/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/ContinuousOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Data/Set/Function.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/MetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch04/.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/local-references/12153e28d102be5e/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/DisjointCover.lean`
- `/tmp/ch04-ptf-decomp/Assembly.lean`
- `/tmp/ch04-ptf-decomp/Frozen1.lean`
- `/tmp/ch04-ptf-decomp/Frozen23.lean`
- `/tmp/ch04-ptf-decomp/simroot2/GMT/Ch04/Submission.lean`
- `/tmp/ch04-ptf-decomp/scripts/sim.py`
- `/tmp/ch04-ptf-decomp/scripts/gen.py`

Contract and proof base:
- The snapshot Contract.lean and the workspace Contract.lean and Submission.lean all have sha256 6e58e5dd…0f4770b.
- The node's proof base 2cce8097 changes no Lean or Lake input (empty diff from ff75f52).

Pinned Mathlib 25730c7c — present and used (snapshot path:line):
- NormedRing.inverse_continuousAt (Analysis/Normed/Ring/Units.lean:183)
- Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Analysis/InnerProductSpace/Projection/Basic.lean:180)
- ContinuousLinearMap.isUnit_iff_bijective (Analysis/Normed/Operator/Banach.lean:459)
- LinearMap.injective_iff_surjective (LinearAlgebra/FiniteDimensional/Basic.lean:308)
- Ring.mul_inverse_cancel (Algebra/GroupWithZero/Units/Basic.lean:99)
- Continuous/ContinuousAt.clm_comp (Analysis/Normed/Operator/BoundedLinearMaps.lean:448–459)
- continuousOn_iff' (Topology/ContinuousOn.lean:124; cite as _root_.continuousOn_iff' under open Metric)
- ContinuousOn.measurable_piecewise (MeasureTheory/Constructions/BorelSpace/Basic.lean:523)
- Measurable.find (MeasureTheory/MeasurableSpace/Constructions.lean:515)
- Measurable.stronglyMeasurable (MeasureTheory/Function/StronglyMeasurable/Basic.lean:691)
- ContinuousLinearMap.instMeasurableSpace / instBorelSpace (MeasureTheory/Constructions/BorelSpace/ContinuousLinearMap.lean:47,50)
- Function.invFunOn_mem / invFunOn_eq and Set.InjOn.leftInvOn_invFunOn (Data/Set/Function.lean:963,966,987)
- LipschitzOnWith.of_dist_le_mul (Topology/MetricSpace/Lipschitz.lean:57)
- InnerProductSpace.toDual with toDual_symm_apply, and ContinuousLinearMap.toSesqForm with toSesqForm_apply_coe, plus ContinuousLinearMap.compSL.
All of these resolve under the frozen imports (#check under import GMT.Ch04.Submission alone).

Unavailable under the frozen imports:
- ContinuousLinearMap.adjoint and LinearMap.adjoint (Analysis/InnerProductSpace/Adjoint.lean:112) are unknown constants.
- The controller's leaf_verification.check_source_delta rejects any added import, so a leaf cannot bring them in.
- Hence child 1 rebuilds Mathlib's adjointAux from toDual and toSesqForm.

No-match results:
- No Mathlib or SimonGMT lemma gives continuity of A ↦ (range A).starProjection. ContinuousLinearMap.isOpen_injective (FiniteDimension.lean:263) exists but is not needed.
- No ready-made countable pasting lemma for relatively continuous fields exists beyond the Measurable.find and measurable_piecewise ingredients.
- SimonGMT offers only an a.e.-measurability transfer (Chapter03.aemeasurable_starProjection_of_approximateTangentField, Rectifiable.lean:260), which does not apply here.

Elaboration and proof checks:
- The three child types pass validate_lean_statement and elaborate as comparator NodeChallenge files in contract scope.
- The parent's frozen type follows from them (Assembly.lean).
- Complete frozen-import proofs of all three children and the parent assembly pass check_source_delta as single-theorem insertions and compile in a copy of Submission.lean. The comparator-style solutions use axioms propext, Classical.choice and Quot.sound only.
- Instance resolution is unchanged by extra imports.
- The proposed names are unused in dag.json, nodes/ and all git refs.
