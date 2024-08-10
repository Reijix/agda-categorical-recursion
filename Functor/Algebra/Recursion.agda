open import Categories.Category.Core
open import Categories.Functor using (Endofunctor; Functor)
open import Categories.Object.Initial using (Initial)
open import Categories.Category.Construction.F-Algebras
open import Categories.Functor.Algebra using (F-Algebra; F-Algebra-Morphism)

import Categories.Morphism.Reasoning as MR

-- paper: file:///home/leonv/Downloads/INF10102-2.pdf
-- interesting: https://webspace.science.uu.nl/~swier004/publications/2018-tyde.pdf

module Functor.Algebra.Recursion {o ℓ e} {C : Category o ℓ e} {F : Endofunctor C} (initial : Initial (F-Algebras F)) where
  open Category C
  open Initial initial
  open F-Algebra ⊥ using () renaming (A to μF; α to inF)
  private
    module F = Functor F
  open HomReasoning
  open Equiv
  open MR C
  open F using (F₀; F₁)

  abstract
    ⦅_⦆ : ∀ {X} → (F₀ X ⇒ X) → (μF ⇒ X)
    ⦅_⦆ {X} φ = F-Algebra-Morphism.f (! {record { A = X ; α = φ }})

    cata-cancel : ∀ {X} {φ : F₀ X ⇒ X} → ⦅ φ ⦆ ∘ inF ≈ φ ∘ F₁ ⦅ φ ⦆
    cata-cancel {X} {φ} = F-Algebra-Morphism.commutes !

    -- entails cata-charn
    cata-unique : ∀ {X} {φ : F₀ X ⇒ X} {f : μF ⇒ X} → f ∘ inF ≈ φ ∘ F₁ f → ⦅ φ ⦆ ≈ f
    cata-unique {X} {φ} {f} f-cancel = !-unique (record { f = f ; commutes = f-cancel })

    cata-refl : ⦅ inF ⦆ ≈ id {μF}
    cata-refl = cata-unique (id-comm-sym ○ ∘-resp-≈ʳ (sym F.identity))

    cata-fusion : ∀ {X Y} {φ : F₀ X ⇒ X} {ψ : F₀ Y ⇒ Y} {f : X ⇒ Y} → f ∘ φ ≈ ψ ∘ F₁ f → ⦅ ψ ⦆ ≈ f ∘ ⦅ φ ⦆
    cata-fusion {X} {Y} {φ} {ψ} {f} eq = cata-unique (begin 
      (f ∘ ⦅ φ ⦆) ∘ inF   ≈⟨ pullʳ cata-cancel ⟩ 
      f ∘ φ ∘ F₁ ⦅ φ ⦆    ≈⟨ extendʳ eq ⟩ 
      ψ ∘ F₁ f ∘ F₁ ⦅ φ ⦆ ≈˘⟨ refl⟩∘⟨ F.homomorphism ⟩ 
      ψ ∘ F₁ (f ∘ ⦅ φ ⦆)  ∎)
