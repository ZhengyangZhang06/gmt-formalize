<!-- theorem-id: gmt-ch06/root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.comparison-a1 -->

## Theorem `Submission.dph_lpf_comparison`

The following notation is that of the frozen statement of the sibling smooth_homotopy, quoted here: Notation: for s ∈ ℝ and x ∈ ℝ^m, cons(s, x) := (EuclideanSpace.equiv (Fin (m+1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x)) ∈ ℝ^{m+1}; ι(v) := cons(0, v); e₀ := EuclideanSpace.single 0 1 ∈ ℝ^{m+1}; for y ∈ ℝ^{m+1}, t(y) := EuclideanSpace.equiv (Fin (m+1)) ℝ y 0 and tl(y) := (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m+1)) ℝ y)); cyl(A) := {y : t(y) ∈ [0,1], tl(y) ∈ A}. D_q(ℝ^p) := GeometricCurrentOn univ q, D^q(ℝ^p) := TestFormOn univ q, M = mass, spt = support, ∂ = boundary. For X ∈ D_k(ℝ^m) and Z ∈ D_{k+1}(ℝ^{m+1}), ProdChar(X, Z) means: for every η ∈ D^{k+1}(ℝ^{m+1}) and every φ : ℝ → D^k(ℝ^m) with φ(s)(x)(v_1, …, v_k) = η(cons(s, x))(e₀, ι(v_1), …, ι(v_k)) for all s ∈ [0,1], x ∈ ℝ^m, v ∈ (ℝ^m)^k (Fin.cons e₀ (ι ∘ v)), one has Z(η) = ∫_0^1 X(φ(s)) ds (interval integral). For g : ℝ^p → ℝ^q, ω ∈ D^j(ℝ^q), η ∈ D^j(ℝ^p) and A ⊆ ℝ^p, 'η is compatible with (g, ω) near A' means: there is an open N ⊇ A with η(x) = ω(g(x)).compContinuousLinearMap (fderiv ℝ g x) for all x ∈ N. Here dω is exteriorDerivative ω. (E0) For all m, m′ ∈ ℕ, X ∈ D_0(ℝ^m) with M(X) < ∞, Z ∈ D_{0+1}(ℝ^{m+1}) with ProdChar(X, Z), and C^∞ G : ℝ^{m+1} → ℝ^{m′} with G⁻¹(K) ∩ cyl(spt X) compact for every compact K: for every ω ∈ D^0(ℝ^{m′}), all η₀, η₁ ∈ D^0(ℝ^m) such that η_i is compatible with (x ↦ G(cons(i, x)), ω) near spt X (i = 0, 1), and every η′ ∈ D^{0+1}(ℝ^{m+1}) compatible with (G, dω) near cyl(spt X): X(η₁) − X(η₀) = Z(η′). (E1) For all m, m′, j ∈ ℕ, X ∈ D_{j+1}(ℝ^m) with M(X) < ∞, Z ∈ D_{j+1+1}(ℝ^{m+1}) with ProdChar(X, Z), Z′ ∈ D_{j+1}(ℝ^{m+1}) with ProdChar(∂X, Z′), and G as in (E0): for every ω ∈ D^{j+1}(ℝ^{m′}), all η₀, η₁ ∈ D^{j+1}(ℝ^m) with η_i compatible with (x ↦ G(cons(i, x)), ω) near spt X, every η′ ∈ D^{j+1+1}(ℝ^{m+1}) compatible with (G, dω) near cyl(spt X) and every θ′ ∈ D^{j+1}(ℝ^{m+1}) compatible with (G, ω) near cyl(spt X): X(η₁) − X(η₀) = Z(η′) + Z′(θ′). (Aff) For all m, m′, k ∈ ℕ there is c ≥ 0 such that for all X ∈ D_k(ℝ^m), Z ∈ D_{k+1}(ℝ^{m+1}), C^∞ maps F₀, F₁ : ℝ^m → ℝ^{m′}, open O ⊆ ℝ^m and s, L, B ∈ ℝ with 0 ≤ s, 0 ≤ L, 0 ≤ B, M(X) ≤ ofReal B, ProdChar(X, Z), spt X ⊆ O, dist(F₁(x), F₀(x)) ≤ s, ‖fderiv ℝ F₀ x‖ ≤ L and ‖fderiv ℝ F₁ x‖ ≤ L for x ∈ O, and F₀⁻¹(K) ∩ spt X compact for every compact K: for every ψ ∈ D^{k+1}(ℝ^{m′}), every C ∈ ℝ with covectorEuclideanNorm (ψ(y)) ≤ C for all y, and every η′ ∈ D^{k+1}(ℝ^{m+1}) compatible near cyl(spt X) with (G, ψ), where G(y) := F₀(tl(y)) + t(y)·(F₁(tl(y)) − F₀(tl(y))), one has |Z(η′)| ≤ c·s·L^k·B·C. Let (SH) denote the conjunction of (E0), (E1) and (Aff) above (verbatim the frozen statement of the sibling smooth_homotopy, Lean name dph_smooth_homotopy), and let (Prod) denote the proposition: for all m, k ∈ ℕ and every X ∈ D_k(ℝ^m) with M(X) < ∞ there is Z ∈ D_{k+1}(ℝ^{m+1}) with ProdChar(X, Z) (this is the existence assertion of part (I) of the frozen statement of the sibling interval_product, dph_interval_product, with its other assertions dropped). C^∞ means ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞), spt = support, and a map g is proper on F if g⁻¹(K) ∩ F is compact for every compact K. Claim: assume (Prod) and (SH). Then for all m, m′, k ∈ ℕ, every X ∈ D_k(ℝ^m) with M(X) < ∞ such that M(∂Y) < ∞ for every j ∈ ℕ and Y ∈ D_{j+1}(ℝ^m) with k = j + 1 and HEq Y X, every G : ℝ^m → ℝ^{m′} proper on spt X, all sequences (G_n), (G′_n) of C^∞ maps ℝ^m → ℝ^{m′}, all open O, O′ ⊆ ℝ^m with spt X ⊆ O and spt X ⊆ O′, and all L, L′ ∈ ℝ such that eventually ‖fderiv ℝ G_n x‖ ≤ L for all x ∈ O, eventually ‖fderiv ℝ G′_n x‖ ≤ L′ for all x ∈ O′, G_n → G uniformly on O and G′_n → G uniformly on O′, and for every ω ∈ D^k(ℝ^{m′}) and all sequences (η_n), (η′_n) in D^k(ℝ^m) such that eventually η_n is compatible with (G_n, ω) near spt X and eventually η′_n is compatible with (G′_n, ω) near spt X: X(η′_n) − X(η_n) → 0 as n → ∞.

Node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.comparison-a1`

Root: https://github.com/ZhengyangZhang06/gmt-formalize/issues/6

Parent: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5257

Prerequisites: https://github.com/ZhengyangZhang06/gmt-formalize/issues/5550, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2493, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2732

Decomposition children: https://github.com/ZhengyangZhang06/gmt-formalize/issues/2493, https://github.com/ZhengyangZhang06/gmt-formalize/issues/2732, https://github.com/ZhengyangZhang06/gmt-formalize/issues/1189, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5858, https://github.com/ZhengyangZhang06/gmt-formalize/issues/5874

## Lean problem

Declaration: `Submission.dph_lpf_comparison`

```lean
(∀ (m k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) k), X.mass < ∞ → ∃ Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (k + 1), ∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) k), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin k → Eucl m), (φ s : DifferentialForm (Eucl m) k) x v = (η : DifferentialForm (Eucl (m + 1)) (k + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s)) → ((∀ (m m' : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) 0) (Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (0 + 1)) (G : Eucl (m + 1) → Eucl m'), X.mass < ∞ → (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (0 + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) 0), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin 0 → Eucl m), (φ s : DifferentialForm (Eucl m) 0) x v = (η : DifferentialForm (Eucl (m + 1)) (0 + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s)) → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support})) → ∀ (ω : TestFormOn (univ : Set (Eucl m')) 0) (η₀ η₁ : TestFormOn (univ : Set (Eucl m)) 0) (η' : TestFormOn (univ : Set (Eucl (m + 1))) (0 + 1)), (∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η₀ : DifferentialForm (Eucl m) 0) x = ((ω : DifferentialForm (Eucl m') 0) ((fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)).compContinuousLinearMap (fderiv ℝ (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)) → (∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η₁ : DifferentialForm (Eucl m) 0) x = ((ω : DifferentialForm (Eucl m') 0) ((fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)).compContinuousLinearMap (fderiv ℝ (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)) → (∃ N : Set (Eucl (m + 1)), IsOpen N ∧ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} ⊆ N ∧ ∀ x ∈ N, (η' : DifferentialForm (Eucl (m + 1)) (0 + 1)) x = ((exteriorDerivative (ω : DifferentialForm (Eucl m') 0)) (G x)).compContinuousLinearMap (fderiv ℝ G x)) → X η₁ - X η₀ = Z η') ∧ (∀ (m m' j : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) (j + 1)) (Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (j + 1 + 1)) (Z' : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (j + 1)) (G : Eucl (m + 1) → Eucl m'), X.mass < ∞ → (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) ((j + 1) + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) (j + 1)), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin (j + 1) → Eucl m), (φ s : DifferentialForm (Eucl m) (j + 1)) x v = (η : DifferentialForm (Eucl (m + 1)) ((j + 1) + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s)) → (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (j + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) j), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin j → Eucl m), (φ s : DifferentialForm (Eucl m) j) x v = (η : DifferentialForm (Eucl (m + 1)) (j + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z' η = ∫ s in (0 : ℝ)..1, X.boundary (φ s)) → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support})) → ∀ (ω : TestFormOn (univ : Set (Eucl m')) (j + 1)) (η₀ η₁ : TestFormOn (univ : Set (Eucl m)) (j + 1)) (η' : TestFormOn (univ : Set (Eucl (m + 1))) (j + 1 + 1)) (θ' : TestFormOn (univ : Set (Eucl (m + 1))) (j + 1)), (∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η₀ : DifferentialForm (Eucl m) (j + 1)) x = ((ω : DifferentialForm (Eucl m') (j + 1)) ((fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)).compContinuousLinearMap (fderiv ℝ (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)) → (∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (η₁ : DifferentialForm (Eucl m) (j + 1)) x = ((ω : DifferentialForm (Eucl m') (j + 1)) ((fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)).compContinuousLinearMap (fderiv ℝ (fun x : Eucl m => G ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 1 (EuclideanSpace.equiv (Fin m) ℝ x)))) x)) → (∃ N : Set (Eucl (m + 1)), IsOpen N ∧ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} ⊆ N ∧ ∀ x ∈ N, (η' : DifferentialForm (Eucl (m + 1)) (j + 1 + 1)) x = ((exteriorDerivative (ω : DifferentialForm (Eucl m') (j + 1))) (G x)).compContinuousLinearMap (fderiv ℝ G x)) → (∃ N : Set (Eucl (m + 1)), IsOpen N ∧ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} ⊆ N ∧ ∀ x ∈ N, (θ' : DifferentialForm (Eucl (m + 1)) (j + 1)) x = ((ω : DifferentialForm (Eucl m') (j + 1)) (G x)).compContinuousLinearMap (fderiv ℝ G x)) → X η₁ - X η₀ = Z η' + Z' θ') ∧ (∀ (m m' k : ℕ), ∃ c : ℝ, 0 ≤ c ∧ ∀ (X : GeometricCurrentOn (univ : Set (Eucl m)) k) (Z : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (k + 1)) (F₀ F₁ : Eucl m → Eucl m') (O : Set (Eucl m)) (s L B : ℝ), 0 ≤ s → 0 ≤ L → 0 ≤ B → X.mass ≤ ENNReal.ofReal B → (∀ (η : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1)) (φ : ℝ → TestFormOn (univ : Set (Eucl m)) k), (∀ s ∈ Icc (0 : ℝ) 1, ∀ (x : Eucl m) (v : Fin k → Eucl m), (φ s : DifferentialForm (Eucl m) k) x v = (η : DifferentialForm (Eucl (m + 1)) (k + 1)) ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons s (EuclideanSpace.equiv (Fin m) ℝ x))) (Fin.cons (EuclideanSpace.single 0 1) fun i => (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm (Fin.cons 0 (EuclideanSpace.equiv (Fin m) ℝ (v i))))) → Z η = ∫ s in (0 : ℝ)..1, X (φ s)) → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₀ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F₁ → IsOpen O → X.support ⊆ O → (∀ x ∈ O, dist (F₁ x) (F₀ x) ≤ s) → (∀ x ∈ O, ‖fderiv ℝ F₀ x‖ ≤ L) → (∀ x ∈ O, ‖fderiv ℝ F₁ x‖ ≤ L) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (F₀ ⁻¹' K ∩ X.support)) → ∀ (ψ : TestFormOn (univ : Set (Eucl m')) (k + 1)) (C : ℝ) (η' : TestFormOn (univ : Set (Eucl (m + 1))) (k + 1)), (∀ y, covectorEuclideanNorm ((ψ : DifferentialForm (Eucl m') (k + 1)) y) ≤ C) → (∃ N : Set (Eucl (m + 1)), IsOpen N ∧ {y : Eucl (m + 1) | EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0 ∈ Icc (0 : ℝ) 1 ∧ (EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y)) ∈ X.support} ⊆ N ∧ ∀ x ∈ N, (η' : DifferentialForm (Eucl (m + 1)) (k + 1)) x = ((ψ : DifferentialForm (Eucl m') (k + 1)) ((fun y : Eucl (m + 1) => F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) + (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) • (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) - F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) x)).compContinuousLinearMap (fderiv ℝ (fun y : Eucl (m + 1) => F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) + (EuclideanSpace.equiv (Fin (m + 1)) ℝ y 0) • (F₁ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))) - F₀ ((EuclideanSpace.equiv (Fin m) ℝ).symm (Fin.tail (EuclideanSpace.equiv (Fin (m + 1)) ℝ y))))) x)) → |Z η'| ≤ c * s * L ^ k * B * C)) → (∀ (m m' k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl m)) k) (G : Eucl m → Eucl m'), X.mass < ∞ → (∀ (j : ℕ) (Y : GeometricCurrentOn (univ : Set (Eucl m)) (j + 1)), k = j + 1 → HEq Y X → Y.boundary.mass < ∞) → (∀ K : Set (Eucl m'), IsCompact K → IsCompact (G ⁻¹' K ∩ X.support)) → ∀ (Gj Gj' : ℕ → Eucl m → Eucl m') (O O' : Set (Eucl m)) (L L' : ℝ), IsOpen O → X.support ⊆ O → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj n)) → (∀ᶠ n in atTop, ∀ x ∈ O, ‖fderiv ℝ (Gj n) x‖ ≤ L) → TendstoUniformlyOn Gj G atTop O → IsOpen O' → X.support ⊆ O' → (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Gj' n)) → (∀ᶠ n in atTop, ∀ x ∈ O', ‖fderiv ℝ (Gj' n) x‖ ≤ L') → TendstoUniformlyOn Gj' G atTop O' → ∀ (ω : TestFormOn (univ : Set (Eucl m')) k) (ηj ηj' : ℕ → TestFormOn (univ : Set (Eucl m)) k), (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (ηj n : DifferentialForm (Eucl m) k) x = ((ω : DifferentialForm (Eucl m') k) (Gj n x)).compContinuousLinearMap (fderiv ℝ (Gj n) x)) → (∀ᶠ n in atTop, ∃ N : Set (Eucl m), IsOpen N ∧ X.support ⊆ N ∧ ∀ x ∈ N, (ηj' n : DifferentialForm (Eucl m) k) x = ((ω : DifferentialForm (Eucl m') k) (Gj' n x)).compContinuousLinearMap (fderiv ℝ (Gj' n) x)) → Tendsto (fun n => X (ηj' n) - X (ηj n)) atTop (𝓝 0))
```

### Frozen project context

`GMT/Ch06/Contract.lean` at `d8d46c9587747dee0751a1f780fcafdba16a3886` supplies the original imports, definitions and root contract. Child hypotheses are stated above; prerequisite declarations are linked in their issues.

```lean
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.EMetricSpace.Lipschitz
import Poincare.SimonGMT.Chapter01.Densities
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter06.Mass
import Poincare.SimonGMT.Chapter06.FormsDuality
import Poincare.SimonGMT.Chapter06.CurrentLocalEquality

/-!
# Simon, *Introduction to Geometric Measure Theory*, Chapter 6 "Currents" (pp. 131–180)

Frozen contract.  Currents, boundary, mass and weak convergence are the clean SimonGMT
objects (`Poincare.SimonGMT.Chapter06`):

* `GeometricCurrentOn U n`: sequentially continuous linear functionals on `𝒟ⁿ(U)` (Simon 2.1);
* `T.boundary` (2.3), `T.massOn W` (2.5, Euclidean coefficient norm of Remark 2.6),
  `T.mass = T.massOn U` (2.4), `T.support` (2.11), `WeaklyConvergesOn` (2.13).

Integer multiplicity currents `τ(M, θ, ξ)` (3.1), restriction `T ⌞ A` (2.9), slices (4.6),
the Lipschitz push-forward (3.6), lattice polyhedral chains (§5) and the flat pseudometric
`d_W` (7.1) are defined below from primitive data.  Hausdorff measure `Hⁿ` is Mathlib's
normalized `μHE[n]` (equal to Lebesgue measure on `ℝⁿ`).

**Degree convention.**  `GeometricCurrentOn.boundary` is defined on degree `m + 1`.  Whenever
the book's statement involves `∂T` for an `n`-current with `n ≥ 1`, the Lean statement writes
the book's `n` as `m + 1`.  The ambient space is `ℝ^P` (book: `ℝ^P` in §2, §8, `ℝ^{n+ℓ}`
elsewhere); in §5–§6, where constants are `c(n, ℓ)`, the ambient space is `ℝ^{(m+1)+ℓ}`.
-/

open MeasureTheory Filter Set Metric
open scoped ENNReal NNReal Topology

namespace GMT.Ch06

open Poincare.SimonGMT.Chapter06
open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasWeightedApproximateTangentSpaceAt)
open Poincare.SimonGMT.Chapter01 (dimensionalUpperDensity)

noncomputable section

/-- Euclidean space `ℝ^P`. -/
abbrev Eucl (P : ℕ) := EuclideanSpace ℝ (Fin P)

variable {P : ℕ}

/-! ## Basic notions -/

/-- Simon's `W ⊂⊂ U` for open `W`: `W` is open and `closure W` is a compact subset of `U`. -/
def CompactlyContainedOpen (W U : Set (Eucl P)) : Prop :=
  IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ U

/-- Simon Ch. 6, 3.1 (p. 146) and 8.1 (p. 173): the conditions on the triple `(M, θ, ξ)`.

* `M ⊆ U` is `Hⁿ`-measurable and countably `n`-rectifiable (Ch. 3, 1.1);
* `θ` is positive on `M` and locally `Hⁿ`-integrable on `M` in `U`;
* `ξ : M → Λₙ(ℝ^P)` is `Hⁿ`-measurable and for `Hⁿ`-a.e. `x ∈ M`, `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` for an
  orthonormal basis `τ` of the approximate tangent space `TₓM` of `M` (w.r.t. `θ`, Ch. 3, 1.7).

`n`-vectors are `NVector (ℝ^P) n` (the dual of `n`-covectors), so `⟨ω, ξ⟩ = ξ ω` and
`τ₁ ∧ ⋯ ∧ τₙ = simpleNVector τ`.  The sign `±` (as printed in 8.1) is only needed for `n = 0`,
where there is no frame to flip. -/
structure IsRectifiableTriple (U : Set (Eucl P)) (n : ℕ) (M : Set (Eucl P))
    (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n) : Prop where
  subset : M ⊆ U
  nullMeasurableSet : NullMeasurableSet M (μHE[n] : Measure (Eucl P))
  countablyRectifiable : CountablyRectifiable n M
  pos : ∀ x ∈ M, 0 < θ x
  integrableOn : ∀ K : Set (Eucl P), IsCompact K → K ⊆ U →
    IntegrableOn θ (M ∩ K) (μHE[n] : Measure (Eucl P))
  aestronglyMeasurable : AEStronglyMeasurable ξ ((μHE[n] : Measure (Eucl P)).restrict M)
  orients : ∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ∃ τ : Fin n → Eucl P,
    Orthonormal ℝ τ ∧
    HasWeightedApproximateTangentSpaceAt n M θ x (Submodule.span ℝ (range τ)) ∧
    (ξ x = simpleNVector τ ∨ ξ x = -simpleNVector τ)

/-- Simon Ch. 6, 3.1 (‡) (p. 146): `τ(M, θ, ξ)(ω) = ∫_M ⟨ω(x), ξ(x)⟩ θ(x) dHⁿ(x)`. -/
def tauAction (n : ℕ) (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n)
    (ω : DifferentialForm (Eucl P) n) : ℝ :=
  ∫ x in M, θ x * ξ x (ω x) ∂(μHE[n] : Measure (Eucl P))

/-- Simon Ch. 6, 8.1 (p. 173): `T` is *rectifiable*, `T = τ(M, θ, ξ)` with `θ` real-valued
(positive, locally `Hⁿ`-integrable; footnote 4). -/
def IsRectifiableCurrent {U : Set (Eucl P)} {n : ℕ} (T : GeometricCurrentOn U n) : Prop :=
  ∃ (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n),
    IsRectifiableTriple U n M θ ξ ∧ ∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω

/-- Simon Ch. 6, 3.1 (p. 146): `T ∈ 𝒟ₙ(U)` is an *integer multiplicity (rectifiable) current*:
`T = τ(M, θ, ξ)` with `θ` positive integer-valued. -/
def IsIntegerMultiplicity {U : Set (Eucl P)} {n : ℕ} (T : GeometricCurrentOn U n) : Prop :=
  ∃ (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n),
    IsRectifiableTriple U n M θ ξ ∧ (∀ x ∈ M, ∃ k : ℕ, θ x = k) ∧
    ∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω

/-- Integral current (the hypothesis of Simon Ch. 6, 8.2, p. 176): `T` and `∂T` are both integer
multiplicity (both then have locally finite mass). -/
def IsIntegralCurrent {U : Set (Eucl P)} {m : ℕ} (T : GeometricCurrentOn U (m + 1)) : Prop :=
  IsIntegerMultiplicity T ∧ IsIntegerMultiplicity T.boundary

/-! ## Measure representation, restriction, slices -/

/-- Simon Ch. 6, (2.7) (p. 136): `T(ω) = ∫ ⟨ω, v⟩ dμ`, with `⟨ω, v⟩` `μ`-integrable for every
test form `ω` (testing with `φ dx^α`, `φ = 1` on a compact `K ⊆ U`, this is equivalent to `v`
being locally `μ`-integrable on `U`).  No normalization of `v` is required: such `(μ, v)` exists
iff `T` has locally finite mass (Riesz, Ch. 1, 4.14), and the vector measure `v μ` on `U` is
then uniquely determined by `T`. -/
def IsMeasureRepresentation {U : Set (Eucl P)} {n : ℕ} (T : GeometricCurrentOn U n)
    (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) n) : Prop :=
  ∀ ω : TestFormOn U n, Integrable (fun x => v x ((ω : DifferentialForm (Eucl P) n) x)) μ ∧
    T ω = ∫ x, v x ((ω : DifferentialForm (Eucl P) n) x) ∂μ

/-- Simon Ch. 6, (2.9) (p. 136): `S = T ⌞ A` for a Borel set `A`, i.e.
`S(ω) = ∫_A ⟨ω, T⃗⟩ dμ_T`.  Defined through any representation of `T` as in (2.7); the result
does not depend on the representation (uniqueness of the vector measure `T⃗ μ_T`). -/
def IsRestriction {U : Set (Eucl P)} {n : ℕ} (T : GeometricCurrentOn U n) (A : Set (Eucl P))
    (S : GeometricCurrentOn U n) : Prop :=
  MeasurableSet A ∧ ∃ (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) n),
    IsMeasureRepresentation T μ v ∧
    ∀ ω : TestFormOn U n, S ω = ∫ x in A, v x ((ω : DifferentialForm (Eucl P) n) x) ∂μ

/-- Simon Ch. 6, (2.8) (p. 136): `μ` is the total variation (mass) measure `μ_T` of `T`:
`μ_T(W) = M_W(T)` for every open `W ⊂⊂ U`, and `μ_T` lives on `U`. -/
def IsMassMeasure {U : Set (Eucl P)} {n : ℕ} (T : GeometricCurrentOn U n)
    (μ : Measure (Eucl P)) : Prop :=
  μ Uᶜ = 0 ∧ ∀ W, CompactlyContainedOpen W U → μ W = T.massOn W

/-- Simon Ch. 6, (4.6) (p. 157): the slice `⟨T, f, t₋⟩ = ∂(T ⌞ {f < t}) − (∂T) ⌞ {f < t}`
(sets taken inside `U`), for `T` with `M_W(T) + M_W(∂T) < ∞`. -/
def IsSlice {U : Set (Eucl P)} {m : ℕ} (T : GeometricCurrentOn U (m + 1)) (f : Eucl P → ℝ)
    (t : ℝ) (S : GeometricCurrentOn U m) : Prop :=
  ∃ (A : GeometricCurrentOn U (m + 1)) (B : GeometricCurrentOn U m),
    IsRestriction T {x | x ∈ U ∧ f x < t} A ∧
    IsRestriction T.boundary {x | x ∈ U ∧ f x < t} B ∧
    ∀ ω : TestFormOn U m, S ω = A.boundary ω - B ω

/-! ## Lipschitz push-forward -/

/-- Simon Ch. 6, (3.6) (p. 147) and Ch. 3, 2.1–2.2: `S = f_# T` for `T = τ(M, θ, ξ)` and `f`
locally Lipschitz, `f_# T(ω) = ∫_M ⟨ω(f(x)), (d^M f_x)_# ξ(x)⟩ θ(x) dHⁿ(x)`.

`L x` is any linear map agreeing with `d^M f_x` on `TₓM`; by Ch. 3, §2 (p. 76),
`d^M f_x(τ) = (d/dt) f(x + tτ)|_{t=0}` for `τ ∈ TₓM`, `Hⁿ`-a.e. `x ∈ M`.  As `ξ(x) ∈ Λₙ(TₓM)`,
the integrand only depends on `L x` restricted to `TₓM`, so `S` is uniquely determined. -/
def IsLipschitzPushforward {Q n : ℕ} {U : Set (Eucl P)} {V : Set (Eucl Q)}
    (T : GeometricCurrentOn U n) (f : Eucl P → Eucl Q) (S : GeometricCurrentOn V n) : Prop :=
  ∃ (M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) n)
    (L : Eucl P → (Eucl P →L[ℝ] Eucl Q)),
    IsRectifiableTriple U n M θ ξ ∧ (∀ ω : TestFormOn U n, T ω = tauAction n M θ ξ ω) ∧
    (∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict M), ∀ Tx : Submodule ℝ (Eucl P),
      HasWeightedApproximateTangentSpaceAt n M θ x Tx →
        ∀ v ∈ Tx, HasDerivAt (fun t : ℝ => f (x + t • v)) (L x v) 0) ∧
    ∀ ω : TestFormOn V n, S ω =
      ∫ x in M, θ x * nVectorPushforward n (L x) (ξ x)
        ((ω : DifferentialForm (Eucl Q) n) (f x)) ∂(μHE[n] : Measure (Eucl P))

/-! ## Lattice polyhedral chains (§5) -/

/-- Index of an `n`-face of the cubical lattice in `ℝ^N` (Simon Ch. 6, §5, p. 159): a lattice
point `z ∈ ℤ^N` and the increasing multi-index `α` of the `n` coordinate directions spanned. -/
abbrev LatticeFaceIndex (n N : ℕ) := (Fin N → ℤ) × SimonMultiIndex n N

/-- The closed face `ρ (z + F_α) ∈ 𝓛ₙ(ρ)`, `F_α = {x : xᵢ ∈ [0,1] (i ∈ α), xᵢ = 0 (i ∉ α)}`.
Every closed `n`-face of the decomposition `⋃_z ρ(z + C)` arises from exactly one index. -/
def latticeFace {n N : ℕ} (ρ : ℝ) (F : LatticeFaceIndex n N) : Set (Eucl N) :=
  {x | ∀ i : Fin N,
    (i ∈ range F.2 → ρ * (F.1 i : ℝ) ≤ x i ∧ x i ≤ ρ * ((F.1 i : ℝ) + 1)) ∧
    (i ∉ range F.2 → x i = ρ * (F.1 i : ℝ))}

/-- `[[F]](ω) = ∫_F ⟨ω, e_{α₁} ∧ ⋯ ∧ e_{αₙ}⟩ dHⁿ` (2.2), `F` oriented by its coordinate
directions in increasing order. -/
def latticeFaceAction {n N : ℕ} (ρ : ℝ) (F : LatticeFaceIndex n N)
    (ω : DifferentialForm (Eucl N) n) : ℝ :=
  ∫ x in latticeFace ρ F, ω x (fun j => EuclideanSpace.single (F.2 j) (1 : ℝ))
    ∂(μHE[n] : Measure (Eucl N))

/-- `Pc = ∑_{F ∈ 𝓛ₙ(ρ)} β_F [[F]]` as a current in `U` (the sum is locally finite). -/
def IsLatticeChain {n N : ℕ} {U : Set (Eucl N)} (ρ : ℝ) (β : LatticeFaceIndex n N → ℝ)
    (Pc : GeometricCurrentOn U n) : Prop :=
  ∀ ω : TestFormOn U n, Pc ω = ∑' F, β F * latticeFaceAction ρ F ω

/-! ## Flat pseudometric (§7) -/

/-- Simon Ch. 6, (7.1) (p. 170): `d_W(T₁, T₂) = inf {M_W(S) + M_W(R) : T₁ − T₂ = ∂R + S,
R ∈ 𝒟ₙ₊₁(U), S ∈ 𝒟ₙ(U) integer multiplicity}`. -/
def flatDistance {U : Set (Eucl P)} {n : ℕ} (W : Set (Eucl P))
    (T₁ T₂ : GeometricCurrentOn U n) : ℝ≥0∞ :=
  ⨅ (R : GeometricCurrentOn U (n + 1)) (S : GeometricCurrentOn U n)
    (_ : IsIntegerMultiplicity R ∧ IsIntegerMultiplicity S ∧
      ∀ ω : TestFormOn U n, T₁ ω - T₂ ω = R.boundary ω + S ω),
    S.massOn W + R.massOn W

/-! ## Headline results -/

/-- **Simon Ch. 6, Lemma 2.15 (p. 137).**  If `T_q ∈ 𝒟ₙ(U)` and `sup_q M_W(T_q) < ∞` for each
`W ⊂⊂ U`, there are a subsequence `T_{q'}` and `T ∈ 𝒟ₙ(U)` with `T_{q'} ⇀ T` and
`∫ ⟨ω, T⃗_{q'}⟩ dμ_{T_{q'}} → ∫ ⟨ω, T⃗⟩ dμ_T` for every continuous compactly supported `n`-form
`ω` on `U` (for all representations (2.7) of the `T_{q'}` and of `T`). -/
def CompactnessUnderMassBounds : Prop :=
  ∀ (P n : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : ℕ → GeometricCurrentOn U n,
    (∀ W, CompactlyContainedOpen W U → (⨆ q, (T q).massOn W) < ∞) →
    ∃ (φ : ℕ → ℕ) (T₀ : GeometricCurrentOn U n), StrictMono φ ∧
      WeaklyConvergesOn (fun q => T (φ q)) T₀ ∧
      ∀ ω : Eucl P → Covector (Eucl P) n, Continuous ω → HasCompactSupport ω → tsupport ω ⊆ U →
        ∀ (μ : ℕ → Measure (Eucl P)) (v : ℕ → Eucl P → NVector (Eucl P) n)
          (μ₀ : Measure (Eucl P)) (v₀ : Eucl P → NVector (Eucl P) n),
          (∀ q, IsMeasureRepresentation (T (φ q)) (μ q) (v q)) →
          IsMeasureRepresentation T₀ μ₀ v₀ →
          Tendsto (fun q => ∫ x, v q x (ω x) ∂(μ q)) atTop (𝓝 (∫ x, v₀ x (ω x) ∂μ₀))

/-- **Simon Ch. 6, Theorem 2.34 (Constancy Theorem, p. 142).**  If `U ⊆ ℝⁿ` is open and
connected, `T ∈ 𝒟ₙ(U)` and `∂T = 0`, then `T = c [[U]]` for a constant `c`, where
`[[U]](ω) = ∫_U ⟨ω, e₁ ∧ ⋯ ∧ eₙ⟩ dLⁿ`.  (Book `n = m + 1`.) -/
def ConstancyTheorem : Prop :=
  ∀ (m : ℕ) (U : Set (Eucl (m + 1))), IsOpen U → IsConnected U →
    ∀ T : GeometricCurrentOn U (m + 1), T.boundary = 0 →
      ∃ c : ℝ, ∀ ω : TestFormOn U (m + 1),
        T ω = c * ∫ x in U, (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x
          (fun i => EuclideanSpace.single i (1 : ℝ)) ∂volume

/-- **Simon Ch. 6, Lemma 3.9 (p. 148).**  If `T ∈ 𝒟ₙ(U)` is integer multiplicity,
`f : U → V` (`V ⊆ ℝ^Q` open) is locally Lipschitz and `f | spt T` is proper, then the
push-forward `f_# T` of (3.6) exists in `𝒟ₙ(V)` and is integer multiplicity. -/
def LipschitzPushforwardIntegerMultiplicity : Prop :=
  ∀ (P Q n : ℕ) (U : Set (Eucl P)) (V : Set (Eucl Q)), IsOpen U → IsOpen V →
    ∀ (T : GeometricCurrentOn U n) (f : Eucl P → Eucl Q),
      IsIntegerMultiplicity T → LocallyLipschitzOn U f → MapsTo f U V →
      (∀ K, IsCompact K → K ⊆ V → IsCompact (f ⁻¹' K ∩ T.support)) →
      ∃ S : GeometricCurrentOn V n, IsLipschitzPushforward T f S ∧ IsIntegerMultiplicity S

/-- **Simon Ch. 6, Theorem 3.11 (Federer–Fleming Compactness Theorem, p. 149).**  If
`T_j ∈ 𝒟ₙ(U)` are integer multiplicity and `sup_j (M_W(T_j) + M_W(∂T_j)) < ∞` for all
`W ⊂⊂ U`, then some subsequence converges weakly in `U` to an integer multiplicity
`T ∈ 𝒟ₙ(U)`.  (Book `n = m + 1`.) -/
def FedererFlemingCompactness : Prop :=
  ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : ℕ → GeometricCurrentOn U (m + 1),
    (∀ j, IsIntegerMultiplicity (T j)) →
    (∀ W, CompactlyContainedOpen W U → (⨆ j, ((T j).massOn W + (T j).boundary.massOn W)) < ∞) →
    ∃ (φ : ℕ → ℕ) (T₀ : GeometricCurrentOn U (m + 1)), StrictMono φ ∧
      IsIntegerMultiplicity T₀ ∧ WeaklyConvergesOn (fun j => T (φ j)) T₀

/-- **Simon Ch. 6, §4 Slicing (4.4–4.10, pp. 153–158).**  Let `T ∈ 𝒟ₙ(U)` with
`M_W(T) + M_W(∂T) < ∞` for all `W ⊂⊂ U`, and `f` Lipschitz on `U` (constant `L`).  Then the
slices `⟨T, f, t⟩ = ∂(T ⌞ {f < t}) − (∂T) ⌞ {f < t}` (4.6) exist for every `t`, satisfy
`spt ⟨T, f, t⟩ ⊆ spt T ∩ {f = t}` (4.8); if `T` is integer multiplicity they are integer
multiplicity for `L¹`-a.e. `t` (4.4, 4.5(2)); and for every open `W ⊆ U`, every `L_W` with
`|Df| ≤ L_W` a.e. on `W` (i.e. `L_W ≥ ess sup_W |Df|`) and `a < b` (4.10, upper integral):
`∫*_a^b M_W(⟨T, f, t⟩) dt ≤ L_W · M_W(T ⌞ {a < f < b})`.
The book prints `M(T ⌞ {a < f < b})` on the right of 4.10; its proof (4.9) gives the stronger
`M_W`, stated here.  (Book `n = m + 1`.) -/
def SlicingTheorem : Prop :=
  ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : GeometricCurrentOn U (m + 1),
    (∀ W, CompactlyContainedOpen W U → T.massOn W < ∞ ∧ T.boundary.massOn W < ∞) →
    ∀ (f : Eucl P → ℝ) (L : ℝ≥0), LipschitzOnWith L f U →
    ∃ S : ℝ → GeometricCurrentOn U m,
      (∀ t, IsSlice T f t (S t)) ∧
      (∀ t, (S t).support ⊆ T.support ∩ {x | f x = t}) ∧
      (IsIntegerMultiplicity T → ∀ᵐ t ∂(volume : Measure ℝ), IsIntegerMultiplicity (S t)) ∧
      ∀ W, IsOpen W → W ⊆ U →
      ∀ LW : ℝ≥0, (∀ᵐ x ∂(volume : Measure (Eucl P)), x ∈ W → ‖fderiv ℝ f x‖₊ ≤ LW) →
      ∀ a b : ℝ, a < b →
        ∀ R : GeometricCurrentOn U (m + 1), IsRestriction T {x | x ∈ U ∧ a < f x ∧ f x < b} R →
          ∃ g : ℝ → ℝ≥0∞, Measurable g ∧ (∀ t ∈ Ioo a b, (S t).massOn W ≤ g t) ∧
            ∫⁻ t in Ioo a b, g t ≤ (LW : ℝ≥0∞) * R.massOn W

/-- **Simon Ch. 6, 5.3 (Deformation Theorem, scaled version, p. 160); `ρ = 1` is 5.1 (p. 159).**
For `n, ℓ ≥ 1` there is `C = C(n, ℓ)` such that for every `T ∈ 𝒟ₙ(ℝ^{n+ℓ})` with
`M(T) + M(∂T) < ∞` and every `ρ > 0`, `T − P = ∂R + S` where `P = ∑_{F ∈ 𝓛ₙ(ρ)} β_F [[F]]`,
`M(P) ≤ C M(T)`, `M(∂P) ≤ C M(∂T)`, `M(R) ≤ C ρ M(T)`, `M(S) ≤ C ρ M(∂T)`,
`spt P ∪ spt R ⊆ {dist(·, spt T) < 2√(n+ℓ) ρ}`, `spt ∂P ∪ spt S ⊆ {dist(·, spt ∂T) < 2√(n+ℓ) ρ}`;
if `T` is integer multiplicity, `P, R` are integer multiplicity with `β_F ∈ ℤ`, and if moreover
`∂T` is integer multiplicity then so is `S`.
Errata: the book prints `n, k ∈ {1,2,…}` and `C(n, k)` for `n, ℓ`; `𝓛_j(ρ)` for `𝓛ₙ(ρ)`;
"so is s" for "so is S".  (Book `n = m + 1`.) -/
def DeformationTheorem : Prop :=
  ∀ m ℓ : ℕ, 1 ≤ ℓ → ∃ C : ℝ≥0, ∀ (T : GeometricCurrentOn (univ : Set (Eucl (m + 1 + ℓ))) (m + 1)),
    T.mass + T.boundary.mass < ∞ → ∀ ρ : ℝ, 0 < ρ →
    ∃ (Pc : GeometricCurrentOn (univ : Set (Eucl (m + 1 + ℓ))) (m + 1))
      (β : LatticeFaceIndex (m + 1) (m + 1 + ℓ) → ℝ)
      (R : GeometricCurrentOn (univ : Set (Eucl (m + 1 + ℓ))) (m + 2))
      (S : GeometricCurrentOn (univ : Set (Eucl (m + 1 + ℓ))) (m + 1)),
      IsLatticeChain ρ β Pc ∧
      (∀ ω, T ω - Pc ω = R.boundary ω + S ω) ∧
      Pc.mass ≤ C * T.mass ∧ Pc.boundary.mass ≤ C * T.boundary.mass ∧
      R.mass ≤ C * ENNReal.ofReal ρ * T.mass ∧ S.mass ≤ C * ENNReal.ofReal ρ * T.boundary.mass ∧
      Pc.support ∪ R.support ⊆
        thickening (2 * Real.sqrt ((m + 1 + ℓ : ℕ) : ℝ) * ρ) T.support ∧
      Pc.boundary.support ∪ S.support ⊆
        thickening (2 * Real.sqrt ((m + 1 + ℓ : ℕ) : ℝ) * ρ) T.boundary.support ∧
      (IsIntegerMultiplicity T →
        (∀ F, ∃ k : ℤ, β F = k) ∧ IsIntegerMultiplicity Pc ∧ IsIntegerMultiplicity R) ∧
      (IsIntegerMultiplicity T → IsIntegerMultiplicity T.boundary → IsIntegerMultiplicity S)

/-- **Simon Ch. 6, 6.1 (Isoperimetric Theorem, p. 168).**  For `n ≥ 2`, `ℓ ≥ 1` there is
`c = c(n, ℓ)` such that every integer multiplicity `T ∈ 𝒟ₙ₋₁(ℝ^{n+ℓ})` with compact support and
`∂T = 0` bounds an integer multiplicity `R ∈ 𝒟ₙ(ℝ^{n+ℓ})` with compact support and
`M(R)^{(n−1)/n} ≤ c M(T)`.  (Book `n = m + 2`.) -/
def IsoperimetricTheorem : Prop :=
  ∀ m ℓ : ℕ, 1 ≤ ℓ → ∃ c : ℝ≥0, ∀ T : GeometricCurrentOn (univ : Set (Eucl (m + 2 + ℓ))) (m + 1),
    IsIntegerMultiplicity T → IsCompact T.support → T.boundary = 0 →
    ∃ R : GeometricCurrentOn (univ : Set (Eucl (m + 2 + ℓ))) (m + 2),
      IsIntegerMultiplicity R ∧ IsCompact R.support ∧ R.boundary = T ∧
      R.mass ^ (((m + 1 : ℕ) : ℝ) / ((m + 2 : ℕ) : ℝ)) ≤ c * T.mass

/-- **Simon Ch. 6, 6.2 (Weak Polyhedral Approximation Theorem, p. 169).**  For integer
multiplicity `T ∈ 𝒟ₙ(U)`, `U ⊆ ℝ^{n+ℓ}` open, with `M_W(T), M_W(∂T) < ∞` for all `W ⊂⊂ U`,
there are `ρ_k ↓ 0` and `P_k = ∑_{F ∈ 𝓛ₙ(ρ_k)} β^{(k)}_F [[F]]` with `β^{(k)}_F ∈ ℤ` and
`P_k ⇀ T` in `U`.  (Printed `F_n(ρ_k)`, `β_R^{(k)}` mean `𝓛ₙ(ρ_k)`, `β_F^{(k)}`.  Book `n = m + 1`.) -/
def PolyhedralApproximation : Prop :=
  ∀ m ℓ : ℕ, 1 ≤ ℓ → ∀ U : Set (Eucl (m + 1 + ℓ)), IsOpen U →
    ∀ T : GeometricCurrentOn U (m + 1), IsIntegerMultiplicity T →
      (∀ W, CompactlyContainedOpen W U → T.massOn W < ∞ ∧ T.boundary.massOn W < ∞) →
      ∃ (ρ : ℕ → ℝ) (β : ℕ → LatticeFaceIndex (m + 1) (m + 1 + ℓ) → ℤ)
        (Pk : ℕ → GeometricCurrentOn U (m + 1)),
        (∀ k, 0 < ρ k) ∧ Antitone ρ ∧ Tendsto ρ atTop (𝓝 0) ∧
        (∀ k, IsLatticeChain (ρ k) (fun F => (β k F : ℝ)) (Pk k)) ∧
        WeaklyConvergesOn Pk T

/-- **Simon Ch. 6, 6.3 (Boundary Rectifiability Theorem, p. 170).**  If `T ∈ 𝒟ₙ(U)` is integer
multiplicity and `M_W(∂T) < ∞` for all `W ⊂⊂ U` (printed `M(∂T)`), then `∂T` is integer
multiplicity.  (Book `n = m + 1`.) -/
def BoundaryRectifiability : Prop :=
  ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : GeometricCurrentOn U (m + 1),
    IsIntegerMultiplicity T → (∀ W, CompactlyContainedOpen W U → T.boundary.massOn W < ∞) →
    IsIntegerMultiplicity T.boundary

/-- **Simon Ch. 6, Theorem 7.2 (p. 170).**  Let `T, T_j ∈ 𝒟ₙ(U)` be integer multiplicity with
`sup_j (M_W(T_j) + M_W(∂T_j)) < ∞` for all `W ⊂⊂ U`.  Then `T_j ⇀ T` iff `d_W(T_j, T) → 0`
for every `W ⊂⊂ U`.  (Book `n = m + 1`.) -/
def FlatConvergenceIffWeakConvergence : Prop :=
  ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U →
    ∀ (T : GeometricCurrentOn U (m + 1)) (Tj : ℕ → GeometricCurrentOn U (m + 1)),
      IsIntegerMultiplicity T → (∀ j, IsIntegerMultiplicity (Tj j)) →
      (∀ W, CompactlyContainedOpen W U →
        (⨆ j, ((Tj j).massOn W + (Tj j).boundary.massOn W)) < ∞) →
      (WeaklyConvergesOn Tj T ↔
        ∀ W, CompactlyContainedOpen W U →
          Tendsto (fun j => flatDistance W (Tj j) T) atTop (𝓝 0))

/-- **Simon Ch. 6, 8.1 (Rectifiability Theorem, p. 173).**  If `T ∈ 𝒟ₙ(U)` has
`M_W(T) + M_W(∂T) < ∞` for all `W ⊂⊂ U` and the upper density `Θ*ⁿ(μ_T, x) > 0` for `μ_T`-a.e.
`x ∈ U`, then `T = τ(M, θ, ξ)` is rectifiable (with real `θ`).  (Book `n = m + 1`.) -/
def RectifiabilityTheorem : Prop :=
  ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ T : GeometricCurrentOn U (m + 1),
    (∀ W, CompactlyContainedOpen W U → T.massOn W + T.boundary.massOn W < ∞) →
    (∃ μ : Measure (Eucl P), IsMassMeasure T μ ∧
      ∀ᵐ x ∂μ, 0 < dimensionalUpperDensity μ.toOuterMeasure ((m + 1 : ℕ) : ℝ) univ x) →
    IsRectifiableCurrent T

/-- **Simon Ch. 6, Theorem 8.2 (p. 176).**  If `T_j, ∂T_j` are integer multiplicity,
`sup_j (M_W(T_j) + M_W(∂T_j)) < ∞` for all `W ⊂⊂ U` and `T_j ⇀ T ∈ 𝒟ₙ(U)`, then `T` is integer
multiplicity.  (Book `n = m + 1`.) -/
def IntegralityOfWeakLimits : Prop :=
  ∀ (P m : ℕ) (U : Set (Eucl P)), IsOpen U →
    ∀ (Tj : ℕ → GeometricCurrentOn U (m + 1)) (T : GeometricCurrentOn U (m + 1)),
      (∀ j, IsIntegralCurrent (Tj j)) →
      (∀ W, CompactlyContainedOpen W U →
        (⨆ j, ((Tj j).massOn W + (Tj j).boundary.massOn W)) < ∞) →
      WeaklyConvergesOn Tj T → IsIntegerMultiplicity T

end

theorem main_theorem : CompactnessUnderMassBounds ∧ ConstancyTheorem ∧ LipschitzPushforwardIntegerMultiplicity ∧ FedererFlemingCompactness ∧ SlicingTheorem ∧ DeformationTheorem ∧ IsoperimetricTheorem ∧ PolyhedralApproximation ∧ BoundaryRectifiability ∧ FlatConvergenceIffWeakConvergence ∧ RectifiabilityTheorem ∧ IntegralityOfWeakLimits := by sorry

end GMT.Ch06
```

## Natural-language proof

Reviewed mathematical argument; formal verification state: `accepted`.

# Parent-supplied natural-language proof

- Parent DAG node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1`
- Child DAG node: `root.deformation-a1.onto_skeleton-a1.pushforward_homotopy-a1.lipschitz_pushforward-a1.comparison-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: Step 1 (comparison lemma) of the supplied proof of lipschitz_pushforward, with the constants and the ε-argument made explicit. Notation: for maps F₀, F₁ : ℝ^m → ℝ^{m′}, H[F₀, F₁](y) := F₀(tl(y)) + t(y)·(F₁(tl(y)) − F₀(tl(y))) is the affine homotopy appearing in (Aff); for a test form ψ, dψ := exteriorDerivativeTestOn univ _ ψ, whose underlying form is exteriorDerivative ψ; |·| = covectorEuclideanNorm. Assume (Prod) and (SH) and fix m, m′, k, X, G, (G_n), (G′_n), O, O′, L, L′, ω, (η_n), (η′_n) as in the claim.

0. (Preliminaries.)
(i) spt X = univ ∖ zeroRegion(X) is closed, the zero region being open. If k = j + 1, the HEq hypothesis applied to j and Y := X (k = j + 1, HEq X X) gives M(∂X) < ∞; moreover spt ∂X ⊆ spt X by part (1) of the reused support_lemmas (with U := univ), and spt ∂X is closed.
(ii) (Bounded test forms.) For every test form ψ on ℝ^{m′} the function y ↦ |ψ(y)| is continuous (|·| is the square root of a finite sum of squares of the evaluations α ↦ α(e_{I(1)}, …, e_{I(q)}), each continuous linear in α, and ψ is continuous) and vanishes outside the compact set tsupport ψ; hence it is bounded, and there is C_ψ ≥ 0 with |ψ(y)| ≤ C_ψ for all y. Put C₁ := C_{dω} and, if k = j + 1, C₂ := C_ω.
(iii) (Products.) By (Prod) for X there is Z ∈ D_{k+1}(ℝ^{m+1}) with ProdChar(X, Z). If k = j + 1, then ∂X ∈ D_j(ℝ^m) has M(∂X) < ∞, and (Prod) for ∂X gives Z′ ∈ D_{j+1}(ℝ^{m+1}) with ProdChar(∂X, Z′).
(iv) (Constants.) (Aff) for (m, m′, k) gives c ≥ 0; if k = j + 1, (Aff) for (m, m′, j) gives c′ ≥ 0. Put O″ := O ∩ O′ (open, spt X ⊆ O″), L″ := max(max(L, L′), 0) ≥ 0 and B := M(X).toReal ≥ 0, so that M(X) = ENNReal.ofReal B because M(X) < ∞; if k = j + 1 put B′ := M(∂X).toReal ≥ 0, so M(∂X) = ENNReal.ofReal B′. Let C₀ := c·B·C₁ if k = 0 and C₀ := c·L″^{j+1}·B·C₁ + c′·L″^j·B′·C₂ if k = j + 1; then C₀ ≥ 0.
(v) (The affine homotopy.) If F₀, F₁ are C^∞, then H := H[F₀, F₁] is C^∞, because t and tl are continuous linear maps and sums, products with the C^∞ scalar function t, and compositions of C^∞ maps are C^∞. Since t(cons(s, x)) = s and tl(cons(s, x)) = x, we have H(cons(0, x)) = F₀(x) + 0 = F₀(x) and H(cons(1, x)) = F₀(x) + (F₁(x) − F₀(x)) = F₁(x) for all x; i.e. the maps x ↦ H(cons(0, x)) and x ↦ H(cons(1, x)) are F₀ and F₁ (so they also have the same derivatives).
1. (Core estimate.) Claim: let F₀, F₁ : ℝ^m → ℝ^{m′} be C^∞ and s ≥ 0, and assume: dist(F₁(x), F₀(x)) ≤ s, ‖fderiv ℝ F₀ x‖ ≤ L″ and ‖fderiv ℝ F₁ x‖ ≤ L″ for all x ∈ O″; F₀ is proper on spt X; H := H[F₀, F₁] is proper on cyl(spt X); and η₀, η₁ ∈ D^k(ℝ^m) are compatible near spt X with (F₀, ω) and (F₁, ω), respectively. Then |X(η₁) − X(η₀)| ≤ C₀·s.
Proof of the claim. By 0(v), η₀ and η₁ are compatible near spt X with (x ↦ H(cons(0, x)), ω) and (x ↦ H(cons(1, x)), ω), which is the form required in (E0) and (E1). H is C^∞ and proper on cyl(spt X), so the reused compatible_form (with P := m + 1, Q := m′, U := V := univ, A := cyl(spt X), f := H) applied to the test form dω gives η′ ∈ D^{k+1}(ℝ^{m+1}) compatible with (H, dω) near cyl(spt X), where the underlying form of dω is exteriorDerivative ω.
Case k = 0. (E0), applied to X, Z, G := H, ω, η₀, η₁ and η′, gives X(η₁) − X(η₀) = Z(η′). (Aff) for (m, m′, 0), applied to X, Z, F₀, F₁, O″, s, L″, B, ψ := dω, C := C₁ and η′ (its hypotheses are exactly: 0 ≤ s, 0 ≤ L″, 0 ≤ B, M(X) ≤ ENNReal.ofReal B, ProdChar(X, Z), F₀ and F₁ C^∞, O″ open with spt X ⊆ O″, the distance and derivative bounds on O″, F₀ proper on spt X, |dω(y)| ≤ C₁ for all y, and η′ compatible near cyl(spt X) with (H[F₀, F₁], dω)), gives |Z(η′)| ≤ c·s·L″^0·B·C₁ = C₀·s.
Case k = j + 1. The reused compatible_form applied to ω gives also θ′ ∈ D^{j+1}(ℝ^{m+1}) and an open N′ ⊇ cyl(spt X) on which θ′ is compatible with (H, ω). (E1), applied to X, Z, Z′, G := H, ω, η₀, η₁, η′ and θ′, gives X(η₁) − X(η₀) = Z(η′) + Z′(θ′). (Aff) for (m, m′, j + 1), applied to X, Z, ψ := dω, C := C₁ and η′ as in the case k = 0, gives |Z(η′)| ≤ c·s·L″^{j+1}·B·C₁. (Aff) for (m, m′, j) is applied to ∂X, Z′, F₀, F₁, O″, s, L″, B′, ψ := ω, C := C₂ and θ′: its hypotheses hold because M(∂X) ≤ ENNReal.ofReal B′, ProdChar(∂X, Z′) holds, spt ∂X ⊆ spt X ⊆ O″, F₀ is proper on spt ∂X (for compact K, F₀⁻¹(K) ∩ spt ∂X = (F₀⁻¹(K) ∩ spt X) ∩ spt ∂X is the intersection of a compact set with a closed set), and θ′ is compatible with (H, ω) near cyl(spt ∂X) on the same N′ (cyl(spt ∂X) ⊆ cyl(spt X)); it gives |Z′(θ′)| ≤ c′·s·L″^j·B′·C₂. Hence |X(η₁) − X(η₀)| ≤ |Z(η′)| + |Z′(θ′)| ≤ C₀·s. This proves the claim.
2. (Eventual hypotheses.) Fix ε > 0. Each of the following finitely many statements holds for all sufficiently large n, hence all of them hold simultaneously for all n ≥ some n_ε: (a) ‖fderiv ℝ G_n x‖ ≤ L for all x ∈ O and ‖fderiv ℝ G′_n x‖ ≤ L′ for all x ∈ O′ (hypotheses); (b) dist(G(x), G_n(x)) < ε for all x ∈ O and dist(G(x), G′_n(x)) < ε for all x ∈ O′ (uniform convergence, Metric.tendstoUniformlyOn_iff); (c) η_n is compatible with (G_n, ω) near spt X and η′_n is compatible with (G′_n, ω) near spt X (hypotheses).
3. (Applying the core estimate.) Let n ≥ n_ε, F₀ := G_n and F₁ := G′_n; both are C^∞, hence continuous. On O″ we have ‖fderiv ℝ F₀ x‖ ≤ L ≤ L″, ‖fderiv ℝ F₁ x‖ ≤ L′ ≤ L″ and dist(F₁(x), F₀(x)) ≤ dist(F₁(x), G(x)) + dist(G(x), F₀(x)) < 2ε. On spt X ⊆ O″ we have dist(F₀(x), G(x)) ≤ ε and dist(F₁(x), G(x)) ≤ ε; since spt X is closed and G is proper on spt X, part (a) of proper_transfer (g := F₀, d := ε) shows that F₀ is proper on spt X, and part (b) of proper_transfer (d := ε) shows that H[F₀, F₁] is proper on cyl(spt X). The core estimate (step 1) with s := 2ε, η₀ := η_n and η₁ := η′_n gives |X(η′_n) − X(η_n)| ≤ 2C₀·ε.
4. (Conclusion.) Let δ > 0 and ε := δ/(2C₀ + 1) > 0. By steps 2 and 3, for all sufficiently large n, |X(η′_n) − X(η_n) − 0| ≤ 2C₀·ε = δ·2C₀/(2C₀ + 1) < δ. Hence X(η′_n) − X(η_n) → 0. ∎

Formalization remark (not part of the mathematical argument): when (E0)/(E1) and (Aff) are instantiated, take G := the explicit lambda y ↦ F₀(tl y) + t(y)·(F₁(tl y) − F₀(tl y)) exactly as written in (Aff); the endpoint identities of 0(v) are then the function equalities (x ↦ H(cons(0, x))) = F₀ and (x ↦ H(cons(1, x))) = F₁, proved by funext from t(cons(s, x)) = s and tl(cons(s, x)) = x (both hold by rfl), and the compatibility hypotheses of (E0)/(E1) follow by rewriting with them.

## Key steps

1. Preliminaries: spt X closed; M(∂X) < ∞ from the HEq hypothesis with Y := X; spt ∂X ⊆ spt X (support_lemmas); sup bounds C₁ for dω and C₂ for ω; products Z of X and Z′ of ∂X from (Prod); constants c, c′ from (Aff).
2. The affine homotopy H[F₀, F₁] is C^∞ with H(cons(0,·)) = F₀ and H(cons(1,·)) = F₁, so η₀, η₁ are compatible in the form required by (E0)/(E1).
3. Core estimate: compatible_form gives η′ (for dω) and θ′ (for ω) near cyl(spt X); (E0)/(E1) and (Aff) for X and ∂X give |X(η₁) − X(η₀)| ≤ C₀·s.
4. Eventually: derivative bounds, dist(G_n, G), dist(G′_n, G) < ε on O, O′, compatibility; then dist(G′_n, G_n) < 2ε on O ∩ O′ and proper_transfer gives properness of G_n on spt X and of the homotopy on cyl(spt X).
5. Hence eventually |X(η′_n) − X(η_n)| ≤ 2C₀ε; with ε := δ/(2C₀ + 1) the difference tends to 0.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `python3 over dag.json (662 nodes): statuses, lean_names, statements, candidate commits; grep of all accepted lean_statements for support/boundary-support, locality, pull-back norm, covector-norm smul, bounded-functional current criteria and extDeriv lemmas -> found iwl_cr_support_lemmas, iwl_cr_ce_apply_eq_of_eqOn_nhds_support, iwl_sp_covectorEuclideanNorm_pullback_le, fiw_ims_sc_continuous_of_bound, fiw_tb_ext_covectorNorm_smul, lpf_pic_current_of_dominated_density; no accepted 'bounded linear functional -> current with mass ≤ B' lemma (no match)`
- `python3 over nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1/decomposition-v2.json: frozen lean_statements of the siblings smooth_approx (889 chars), interval_product (5579), smooth_homotopy (8216), identical to dag.json`
- `rg -n 'theorem extDeriv_pullback|theorem Filter.EventuallyEq.extDeriv_eq|theorem TendstoUniformlyOn.congr_right|theorem TendstoUniformly.tendstoUniformlyOn|theorem IsCompact.cthickening|theorem mem_cthickening_of_dist_le|theorem self_subset_thickening|theorem cons_self_tail|theorem tail_cons|theorem cauchySeq_tendsto_of_complete|theorem tendsto_nhds_unique' over the snapshot mathlib/Mathlib (all found: DifferentialForm/Basic.lean:259,188; UniformSpace/UniformConvergence.lean:218,222; MetricSpace/Thickening.lean:283,201,309; Data/Fin/Tuple/Basic.lean:171,117; UniformSpace/Cauchy.lean:425; Separation/Hausdorff.lean:180)`
- `grep -n '^def|^structure|^theorem|^abbrev' over .lake/packages/simongmt/Poincare/SimonGMT/Chapter06/{Currents,Forms,Mass,CurrentLocalEquality}.lean: GeometricCurrentOn (toCurrent, continuous'), TestFormOnConverges, exteriorDerivativeTestOn, GeometricCurrentOn.boundary_apply/boundary_boundary/ext, exteriorDerivative = extDeriv, massAdmissibleOn, massOn, mass, covectorEuclideanNorm, VanishesOn, zeroRegion, support`
- `rg -n 'dph_lpf|LipPF' over the snapshot project and mathlib (*.lean): no match; git log --all -S dph_lpf_ over 3993 refs: no match`
- `read /runtime/flows/gmt-claude-0135a42af877/_recursive_lean/runtime.py (_existing_lean_name_problem, reuse-by-name id mapping, _dependency_problem, _overlay_accepted_children over children+depends_on) and store.py (ensure returns existing nodes unchanged)`
- `git show <candidate> for the 5 reused declarations (fd5f1e29, 02f3305f, 5c248501, ba202ac0, 3e52d3e8): declarations present together with their own accepted prerequisites; isolated-comparator-result.json passed = True for all five`
- `python3 -I verifier/gmt-compare.py contract_scope(GMT/Ch06/Contract.lean, GMT.Ch06.main_theorem); verifier/lean_contract.py validate_lean_statement on all 12 child statements (all valid)`
- `lake env lean /tmp/lpf_decomp/AllStmts.lean (7 child statements + parent; only sorry warnings), /tmp/lpf_decomp/IfaceCheck.lean (parent proved from children + uncles; no errors), /tmp/lpf_decomp/Skel.lean and Endpt.lean (comparison instantiation of (E0),(E1),(Aff), compatible_form, support_lemmas; endpoint identities by rfl), /tmp/lpf_decomp/Checks3.lean (current_criterion fully proved; (dP); mass arithmetic), /tmp/lpf_review/lean/T2-T8.lean (independent full proofs of the new children modulo declared dependencies; exit 0, no errors)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/UniformSpace/UniformConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/MetricSpace/Thickening.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Data/Fin/Tuple/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/UniformSpace/Cauchy.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Topology/Separation/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-lipschit-30886ea76d/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1-lipschit-30886ea76d/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-onto-skeleton-a1-pushforward-homotopy-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-smooth-pushforward-a1-compatible-form-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-cycle-reduction-a1-support-lemmas-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1-series-current-a1-continuity-criterion-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-compactness-mass-bounds-a1-mass-bound-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-smooth-pushforward-a1-pullback-norm-a1/parent-child-handoff.json`
- `/runtime/flows/gmt-claude-0135a42af877/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-0135a42af877/_recursive_lean/store.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/lpf_decomp/AllStmts.lean`
- `/tmp/lpf_decomp/IfaceCheck.lean`
- `/tmp/lpf_decomp/Skel.lean`
- `/tmp/lpf_decomp/Checks3.lean`
- `/tmp/lpf_review/lean/T6.lean`
- `/tmp/lpf_review/lean/T7.lean`

The pinned project and SimonGMT contain no Lipschitz push-forward of normal currents, no products with [[0,1]] and no homotopy formula, so the supplied Parts 1–8 are new obligations. Their smooth-approximation, product and homotopy inputs come from the three unaccepted uncle nodes, which are therefore passed as explicit hypotheses. Five accepted declarations are reused by name with byte-identical types: compatible forms (R3), the support facts (S)/(F3c), the mass bound (R1), the pull-back norm bound (F7), and the continuity criterion for (F5/F6). No accepted lemma already turns a bounded linear functional into a current with a mass bound, so this becomes the new child current_criterion. Every Mathlib lemma cited in the child proofs exists in the pinned snapshot (extDeriv_pullback, EventuallyEq.extDeriv_eq, TendstoUniformlyOn.congr_right, IsCompact.cthickening, mem_cthickening_of_dist_le, self_subset_thickening, Fin.cons_self_tail, cauchySeq_tendsto_of_complete, tendsto_nhds_unique). All statements elaborate in the exact comparator scope. The parent follows from the children by a checked 4-line assembly, and each new child has an independent Lean proof modulo its declared dependencies. The dph_lpf_* names are globally unused.


## Acceptance

The exact contract must pass deterministic Git identity checks and the machine comparator, without a Lean agent review, changed assumptions or proof holes. Every node delivers an immutable accepted candidate after its original proof checks. Parents compose dependencies in isolated worktrees. Only the root integrates and validates the final target tree. Every child retains its issue and review PR.

Solution PR: Pending

After proof acceptance and exact solution PR publication, close this theorem issue. Issue closure does not assert Git merge or final root delivery.

Child PRs remain review records; only confirmed root delivery closes those PRs without merging them.

Proof status (`accepted` / `merged`) and GitHub PR state are separate.
