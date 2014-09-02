{-# OPTIONS --universe-polymorphism #-}

open import Level

module Categories.Terminal {o a : Level} where

open import Categories.Support.PropositionalEquality

open import Categories.Category
open import Categories.Functor
open import Categories.Categories
import Categories.Object.Terminal as Terminal

open Terminal (Categories o a)

record Unit {x : _} : Set x where
  constructor unit

OneC : Category o a
OneC = record 
  { Obj = Unit
  ; _⇒_ = λ _ _ → Unit
  ; _∘_ = λ _ _ → unit
  ; id = unit
  ; ASSOC = λ f g h → ≣-refl
  ; IDENTITYˡ = λ f → unit-unique
  ; IDENTITYʳ = λ f → unit-unique
  }
  where
  unit-unique : ∀ {ℓ} {f g : Unit {ℓ}} → unit ≣ f
  unit-unique {f = unit} {unit} = ≣-refl

-- I can probably use Discrete here once we get universe cumulativity in Agda
One : Terminal
One = record 
  { ⊤ = OneC
  ; ! = my-!
  ; !-unique = λ F → promote my-! F (λ _ → Heterogeneous.≡⇒∼ ≣-refl)
  }
  where
  my-! : ∀ {A} → Functor A OneC
  my-! = record
    { F₀ = λ _ → unit
    ; F₁ = λ _ → unit
    ; identity = ≣-refl
    ; homomorphism = ≣-refl
    }
