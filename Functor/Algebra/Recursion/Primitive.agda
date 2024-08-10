open import Categories.Category.Core
open import Categories.Functor using (Endofunctor; Functor)
open import Categories.Object.Initial using (Initial)
open import Categories.Category.Construction.F-Algebras
open import Categories.Functor.Algebra using (F-Algebra; F-Algebra-Morphism)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Category.BinaryProducts using (BinaryProducts)

import Categories.Morphism.Reasoning as MR

-- paper: file:///home/leonv/Downloads/INF10102-2.pdf

module Functor.Algebra.Recursion.Primitive {o ℓ e} {C : Category o ℓ e} (cartesian : Cartesian C) {F : Endofunctor C} (initial : Initial (F-Algebras F)) where
  open Category C
  open Cartesian cartesian
  open BinaryProducts products
  open Initial initial
  private
    module ⊥ = F-Algebra ⊥
    module F = Functor F
  open HomReasoning
  open Equiv
  open MR C
  open F using (F₀; F₁)

  open import Functor.Algebra.Recursion initial

  abstract
    ⦉_⦊ : ∀ {X} → (F₀ (X × ⊥.A) ⇒ X) → (⊥.A ⇒ X)
    ⦉_⦊ {X} φ = π₁ ∘ ⦅ ⟨ φ , ⊥.α ∘ F₁ π₂ ⟩ ⦆

    para-cancel : ∀ {X} {φ : F₀ (X × ⊥.A) ⇒ X} → ⦉ φ ⦊ ∘ ⊥.α ≈ φ ∘ F₁ ⟨ ⦉ φ ⦊ , id ⟩
    para-cancel {X} {φ} = begin 
      (π₁ ∘ ⦅ ⟨ φ , ⊥.α ∘ F₁ π₂ ⟩ ⦆) ∘ ⊥.α                  ≈⟨ pullʳ cata-cancel ⟩ 
      π₁ ∘ ⟨ φ , ⊥.α ∘ F₁ π₂ ⟩ ∘ F₁ ⦅ ⟨ φ , ⊥.α ∘ F₁ π₂ ⟩ ⦆ ≈⟨ pullˡ project₁ ⟩ 
      φ ∘ F₁ ⦅ ⟨ φ , ⊥.α ∘ F₁ π₂ ⟩ ⦆                        ≈˘⟨ refl⟩∘⟨ F.F-resp-≈ g-η ⟩ 
      φ ∘ F₁ ⟨ ⦉ φ ⦊ , π₂ ∘ ⦅ ⟨ φ , ⊥.α ∘ F₁ π₂ ⟩ ⦆ ⟩       ≈˘⟨ refl⟩∘⟨ (F.F-resp-≈ (⟨⟩-cong₂ refl (cata-fusion project₂))) ⟩ 
      φ ∘ F₁ ⟨ ⦉ φ ⦊ , ⦅ ⊥.α ⦆ ⟩                            ≈⟨ refl⟩∘⟨ F.F-resp-≈ (⟨⟩-cong₂ refl cata-refl) ⟩
      φ ∘ F₁ ⟨ ⦉ φ ⦊ , id ⟩                                 ∎

    para-unique : ∀ {X} {φ : F₀ (X × ⊥.A) ⇒ X} {f : ⊥.A ⇒ X} → f ∘ ⊥.α ≈ φ ∘ F₁ ⟨ f , id ⟩ → ⦉ φ ⦊ ≈ f
    para-unique {X} {φ} {f} f-cancel = begin 
      π₁ ∘ ⦅ ⟨ φ , ⊥.α ∘ F₁ π₂ ⟩ ⦆ ≈⟨ refl⟩∘⟨ cata-unique helper ⟩ 
      π₁ ∘ ⟨ f , id ⟩              ≈⟨ project₁ ⟩ 
      f                            ∎
      where
      helper : ⟨ f , id ⟩ ∘ ⊥.α ≈ ⟨ φ , ⊥.α ∘ F₁ π₂ ⟩ ∘ F₁ ⟨ f , id ⟩
      helper = begin 
        ⟨ f , id ⟩ ∘ ⊥.α                    ≈⟨ ⟨⟩∘ ○ ⟨⟩-cong₂ f-cancel identityˡ ⟩ 
        ⟨ φ ∘ F₁ ⟨ f , id ⟩ , ⊥.α ⟩         ≈˘⟨ ⟨⟩∘ ○ ⟨⟩-cong₂ refl (cancelʳ (sym F.homomorphism ○ F.F-resp-≈ project₂ ○ F.identity)) ⟩ 
        ⟨ φ , ⊥.α ∘ F₁ π₂ ⟩ ∘ F₁ ⟨ f , id ⟩ ∎

    para-refl : ⦉ ⊥.α ∘ F₁ π₁ ⦊ ≈ id
    para-refl = para-unique (id-comm-sym ○ sym (pullʳ (sym F.homomorphism ○ F.F-resp-≈ project₁ ○ F.identity)))

    para-fusion : ∀ {X Y} {φ : F₀ (X × ⊥.A) ⇒ X} {ψ : F₀ (Y × ⊥.A) ⇒ Y} {f : X ⇒ Y} → f ∘ φ ≈ ψ ∘ F₁ (f ⁂ id) → ⦉ ψ ⦊ ≈ f ∘ ⦉ φ ⦊
    para-fusion {X} {Y} {φ} {ψ} {f} eq = para-unique (begin 
      (f ∘ ⦉ φ ⦊) ∘ ⊥.α                   ≈⟨ pullʳ para-cancel ⟩ 
      f ∘ φ ∘ F₁ ⟨ ⦉ φ ⦊ , id ⟩           ≈⟨ extendʳ eq ⟩ 
      ψ ∘ F₁ (f ⁂ id) ∘ F₁ ⟨ ⦉ φ ⦊ , id ⟩ ≈⟨ refl⟩∘⟨ (sym F.homomorphism ○ F.F-resp-≈ (⁂∘⟨⟩ ○ ⟨⟩-cong₂ refl identity²)) ⟩ 
      ψ ∘ F₁ ⟨ f ∘ ⦉ φ ⦊ , id ⟩           ∎)
