{-# OPTIONS --universe-polymorphism #-}
module Categories.Groupoid where

open import Level
open import Data.Product

open import Categories.Category
open import Categories.Product renaming (Product to ℙroduct)
import Categories.Morphisms as M

record Groupoid {o ℓ e} (C : Category o ℓ e) : Set (o ⊔ ℓ ⊔ e) where
  private module C = Category C
  open C using (_⇒_)
  open M C

  field
    _⁻¹  : ∀ {A B} → (A ⇒ B) → (B ⇒ A)
    .iso : ∀ {A B} {f : A ⇒ B} → Iso f (f ⁻¹)
