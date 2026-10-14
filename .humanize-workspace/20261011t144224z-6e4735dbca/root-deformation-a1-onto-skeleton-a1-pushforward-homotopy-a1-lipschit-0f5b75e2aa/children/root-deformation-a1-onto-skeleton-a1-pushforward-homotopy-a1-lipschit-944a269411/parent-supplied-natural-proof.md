# Parent-supplied natural-language proof

- Parent DAG node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.comparison-a1`
- Child DAG node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.comparison-a1.affine_homotopy-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 0(v) of the supplied proof of comparison (the affine homotopy is C^∞ and restricts to F₀ and F₁ at the two ends of the cylinder) together with its formalization remark, with all details filled in. Fix m, m′, F₀, F₁ and G with G = H[F₀, F₁]; substitute this equation (in Lean: subst), so that G is the explicit lambda.

1. (Coordinates of cons.) Let s ∈ ℝ and x ∈ ℝ^m. EuclideanSpace.equiv (Fin (m+1)) ℝ : ℝ^{m+1} ≃L (Fin (m+1) → ℝ) is WithLp.ofLp and its inverse is WithLp.toLp, so EuclideanSpace.equiv (Fin (m+1)) ℝ (cons(s, x)) = Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x) holds definitionally. Hence t(cons(s, x)) = (Fin.cons s _) 0 = s (Fin.cons_zero), and, since Fin.tail (Fin.cons s v) = v (Fin.tail_cons), tl(cons(s, x)) = (EuclideanSpace.equiv (Fin m) ℝ).symm (EuclideanSpace.equiv (Fin m) ℝ x) = x. Both identities t(cons(s, x)) = s and tl(cons(s, x)) = x hold by definitional unfolding (rfl).
2. (Part (a).) By function extensionality it suffices to show G(cons(0, x)) = F₀(x) for every x ∈ ℝ^m. By step 1, G(cons(0, x)) is definitionally F₀(x) + 0·(F₁(x) − F₀(x)); and 0·v = 0 (zero_smul) and F₀(x) + 0 = F₀(x) (add_zero). Lean remark: simp does not rewrite EuclideanSpace.equiv _ _ (WithLp.toLp 2 _), so first restate the goal definitionally, `change F₀ x + (0 : ℝ) • (F₁ x - F₀ x) = F₀ x`, and then `rw [zero_smul, add_zero]`.
3. (Part (b).) Likewise, for x ∈ ℝ^m, G(cons(1, x)) is definitionally F₀(x) + 1·(F₁(x) − F₀(x)), which equals F₀(x) + (F₁(x) − F₀(x)) = F₁(x) (one_smul, add_sub_cancel; in Lean `change F₀ x + (1 : ℝ) • (F₁ x - F₀ x) = F₁ x` first). By funext, (x ↦ G(cons(1, x))) = F₁.
4. (Part (c).) Assume F₀ and F₁ are C^∞.
   (i) The map q ↦ Fin.tail q from (Fin (m+1) → ℝ) to (Fin m → ℝ) is C^∞: by contDiff_pi it suffices that each coordinate q ↦ q(i.succ) is C^∞, which is contDiff_apply.
   (ii) EuclideanSpace.equiv (Fin (m+1)) ℝ and (EuclideanSpace.equiv (Fin m) ℝ).symm are continuous linear equivalences, hence C^∞ (ContinuousLinearEquiv.contDiff). By ContDiff.comp, tl = (EuclideanSpace.equiv (Fin m) ℝ).symm ∘ Fin.tail ∘ EuclideanSpace.equiv (Fin (m+1)) ℝ is C^∞.
   (iii) t = (q ↦ q 0) ∘ EuclideanSpace.equiv (Fin (m+1)) ℝ is C^∞ (contDiff_apply composed with the equivalence).
   (iv) Hence F₀ ∘ tl and F₁ ∘ tl are C^∞ (ContDiff.comp); so are their difference (ContDiff.sub), its product with the C^∞ scalar function t (ContDiff.smul), and the sum F₀ ∘ tl + t·(F₁ ∘ tl − F₀ ∘ tl) (ContDiff.add). This sum is G, so G is C^∞. ∎

## Key steps

1. t(cons(s, x)) = s and tl(cons(s, x)) = x hold definitionally (EuclideanSpace.equiv applied to its inverse, Fin.cons_zero, Fin.tail_cons).
2. Hence G(cons(0, x)) = F₀(x) + 0·(F₁(x) − F₀(x)) = F₀(x) and G(cons(1, x)) = F₀(x) + 1·(F₁(x) − F₀(x)) = F₁(x); conclude by funext (restate the goal with change, as simp does not unfold the equivalences).
3. tl and t are C^∞ (coordinate projections composed with continuous linear equivalences), so G = F₀∘tl + t·(F₁∘tl − F₀∘tl) is C^∞.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `python3 -I over dag.json (685 nodes): lean_statements mentioning covectorEuclideanNorm with an existential bound -> br_la_testForm_covectorNorm_bounded, polyhedral_approx_testForm_covectorNorm_bounded, fiw_ims_sc_testForm_bounded (all accepted, same type); br_la_testForm_covectorNorm_bounded chosen (no prerequisites, candidate c34586955a827a6731d9bc0ca8ae1ba1c0791948, isolated-comparator-result passed = true)`
- `python3 -I over dag.json: dependencies of the selected node -> dph_lpf_proper_transfer (status decomposing, parent lipschitz_pushforward-a1), iwl_sp_exists_compatible_testForm (accepted, fd5f1e29719e3bfa62df774678e3c6879599f8f9), iwl_cr_support_lemmas (accepted, 02f3305faacfc43200f665dd4b67e2a44ab25d0b); titles, statements and lean_statements byte-identical to their handoffs`
- `read /runtime/flows/gmt-claude-0135a42af877/_recursive_lean/runtime.py: _existing_lean_name_problem (an unaccepted node owned by another parent cannot be reused by name), _accepted_checkpoint (status accepted + candidate commit), _dependency_problem/_topological, reuse of accepted children by name`
- `rg over the snapshot mathlib/Mathlib: contDiff_pi and contDiff_apply (Analysis/Calculus/ContDiff/Operations.lean:112,145), ContinuousLinearEquiv.contDiff (Analysis/Calculus/ContDiff/Basic.lean:165), Fin.tail_cons and Fin.cons_zero (Data/Fin/Tuple/Basic.lean:117,129), IsCompact.inter_right (Topology/Compactness/Compact.lean:86), IsClosed.sdiff (Topology/Basic.lean:182), Set.inter_eq_right (Data/Set/Basic.lean:833), ENNReal.ofReal_toReal (Basic/ENNReal/Basic.lean:248), mabs_mul_le = to_additive source of abs_add_le (Algebra/Order/Group/Unbundled/Abs.lean:123), Metric.tendstoUniformlyOn_iff (Topology/MetricSpace/Pseudo/Basic.lean:142), Metric.tendsto_nhds and dist_triangle (Topology/MetricSpace/Pseudo/Defs.lean:888,210), div_lt_one (Algebra/Order/Field/Basic.lean:47): all found`
- `grep over .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/{Forms,Currents,Mass,CurrentLocalEquality}.lean: exteriorDerivative = extDeriv (abbrev), exteriorDerivativeTestOn (toFun ⟨exteriorDerivative ω, _⟩), GeometricCurrentOn.boundary_apply, GeometricCurrentOn.support = U \ zeroRegion, GeometricCurrentOn.isOpen_zeroRegion, covectorEuclideanNorm, massOn/mass`
- `rg -n 'dph_lpf_cmp|cmp_core_estimate|affine_homotopy' over the snapshot project and mathlib, git log --all -S dph_lpf_cmp, and dag.json lean_names: no match (new names unused)`
- `python3 -I verifier/lean_contract.py validate_lean_statement on all 7 statements (valid, single line) and verifier/gmt-compare.py contract_scope(GMT/Ch06/Contract.lean, GMT.Ch06.main_theorem)`
- `lake env lean /tmp/cmp_decomp/Stmts.lean (all statements elaborate), /tmp/cmp_decomp/Full.lean (complete proofs of dph_lpf_cmp_affine_homotopy, dph_lpf_cmp_core_estimate and of dph_lpf_comparison from them plus dph_lpf_proper_transfer; sorry only in the 4 stubbed dependency declarations; affine lemma axioms propext, Classical.choice, Quot.sound); independent reviewer recompiled /tmp/cmp_review/{A_affine,B_core,C_parent}.lean with only declared dependencies in scope`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/ContDiff/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Compactness/Compact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Set/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Basic/ENNReal/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/Order/Group/Unbundled/Abs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Algebra/Order/Field/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-lipschit-0f5b75e2aa/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-lipschit-30886ea76d/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-smooth-pushforward-a1-compatible-form-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-support-lemmas-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-lattice-approximation-a1-testform-bounded-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-lattice-approximation-a1-testform-bounded-a1/isolated-comparator-result.json`
- `/runtime/flows/gmt-claude-0135a42af877/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/cmp_decomp/Stmts.lean`
- `/tmp/cmp_decomp/Full.lean`
- `/tmp/cmp_decomp/proofs/dph_lpf_cmp_affine_homotopy.lean`
- `/tmp/cmp_decomp/proofs/dph_lpf_cmp_core_estimate.lean`
- `/tmp/cmp_decomp/proofs/dph_lpf_comparison.lean`

The pinned project, SimonGMT and Mathlib contain no comparison lemma, affine-homotopy lemma or homotopy-based Lipschitz estimate for currents (no match for the new names anywhere; both are unused in dag.json and git history), so dph_lpf_cmp_core_estimate (supplied Step 1 with 0(ii)–(iv)) and dph_lpf_cmp_affine_homotopy (supplied 0(v)) are new obligations. Three accepted declarations are reused by name with byte-identical types: iwl_sp_exists_compatible_testForm, iwl_cr_support_lemmas and br_la_testForm_covectorNorm_bounded (the prerequisite-free one among three identical accepted bounded-test-form lemmas). proper_transfer is unaccepted and owned by another parent, so it remains a dependency of the selected node and is used only in the parent's ε-argument. All Mathlib/SimonGMT facts used in the child proofs exist in the snapshot; every statement elaborates in the frozen contract scope; both new children have complete Lean proofs modulo their declared dependencies; and the parent compiles from core_estimate and proper_transfer.
