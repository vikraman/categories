{-# OPTIONS --universe-polymorphism #-}
module Category.Monad where

open import Support
open import Category
open import Category.Functor hiding (_≡_; assoc; identityˡ; identityʳ)
open import Category.NaturalTransformation renaming (id to idN)

record Monad {o ℓ e} (C : Category o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
  field
    F : Endofunctor C
    η : NaturalTransformation id F
    μ : NaturalTransformation (F ∘ F) F

  open Functor F

  field
    .assoc     : μ ∘₁ (F ∘ˡ μ) ≡ μ ∘₁ (μ ∘ʳ F)
    .identityˡ : μ ∘₁ (F ∘ˡ η) ≡ idN
    .identityʳ : μ ∘₁ (η ∘ʳ F) ≡ idN