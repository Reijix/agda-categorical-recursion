open import Categories.Category.Core
open import Categories.Functor using (Endofunctor; Functor)
open import Categories.Object.Terminal using (Terminal)
open import Categories.Category.Construction.F-Coalgebras
open import Categories.Functor.Coalgebra using (F-Coalgebra; F-Coalgebra-Morphism)

import Categories.Morphism.Reasoning as MR

module Functor.Coalgebra.Corecursion {o ℓ e} {C : Category o ℓ e} {F : Endofunctor C} (terminal : Terminal (F-Coalgebras F)) where
  open Category C
  open Terminal terminal
  module ⊤ = F-Coalgebra ⊤
  open HomReasoning
  open Equiv
  open MR C
  module F = Functor F
  open F using (F₀; F₁)

  abstract
    ⟦_⟧ : ∀ {X} → (X ⇒ F₀ X) → (X ⇒ ⊤.A)
    ⟦_⟧ {X} φ = F-Coalgebra-Morphism.f (! {record { A = X ; α = φ }})

    ana-cancel : ∀ {X} {φ : X ⇒ F₀ X} → ⊤.α ∘ ⟦ φ ⟧ ≈ F₁ ⟦ φ ⟧ ∘ φ
    ana-cancel {X} {φ} = F-Coalgebra-Morphism.commutes !

    -- entails ana-charn
    ana-unique : ∀ {X} {φ : X ⇒ F₀ X} {f : X ⇒ ⊤.A} → ⊤.α ∘ f ≈ F₁ f ∘ φ → ⟦ φ ⟧ ≈ f
    ana-unique {X} {φ} {f} f-cancel = !-unique (record { f = f ; commutes = f-cancel })

    ana-refl : ⟦ ⊤.α ⟧ ≈ id {⊤.A}
    ana-refl = ana-unique (id-comm ○ ∘-resp-≈ˡ (sym F.identity))

    ana-fusion : ∀ {X Y} {φ : X ⇒ F₀ X} {ψ : Y ⇒ F₀ Y} {f : X ⇒ Y} → ψ ∘ f ≈ F₁ f ∘ φ → ⟦ φ ⟧ ≈ ⟦ ψ ⟧ ∘ f
    ana-fusion {X} {Y} {φ} {ψ} {f} eq = ana-unique (begin 
      ⊤.α ∘ ⟦ ψ ⟧ ∘ f     ≈⟨ extendʳ ana-cancel ⟩ 
      F₁ ⟦ ψ ⟧ ∘ ψ ∘ f    ≈⟨ refl⟩∘⟨ eq ⟩ 
      F₁ ⟦ ψ ⟧ ∘ F₁ f ∘ φ ≈⟨ pullˡ (sym F.homomorphism) ⟩ 
      F₁ (⟦ ψ ⟧ ∘ f) ∘ φ  ∎)
