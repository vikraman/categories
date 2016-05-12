{-# OPTIONS --type-in-type #-}

module Categories.Sum where

open import Level
open import Data.Empty
open import Data.Sum

open import Categories.Category

Sum : ∀ {o ℓ e o′ ℓ′ e′} (C : Category o ℓ e) (D : Category o′ ℓ′ e′) → Category (o ⊔ o′) (ℓ ⊔ ℓ′) (e ⊔ e′)
Sum C D = record
  { Obj = C.Obj ⊎ D.Obj
  ; _⇒_ = λ { (inj₁ c₁) (inj₁ c₂) → C._⇒_ c₁ c₂
            ; (inj₁ c) (inj₂ d) → ⊥
            ; (inj₂ d) (inj₁ c) → ⊥
            ; (inj₂ d₁) (inj₂ d₂) → D._⇒_ d₁ d₂
            }
  ; _≡_ = λ { {inj₁ _} {inj₁ _} → C._≡_
            ; {inj₁ _} {inj₂ _} ()
            ; {inj₂ _} {inj₁ _} ()
            ; {inj₂ _} {inj₂ _} → D._≡_
            }
  ; _∘_ = λ { {inj₁ _} {inj₁ _} {inj₁ _} → C._∘_
            ; {inj₁ _} {inj₁ _} {inj₂ _} → λ z _ → z
            ; {inj₁ _} {inj₂ _} {inj₁ _} → λ _ → λ ()
            ; {inj₁ _} {inj₂ _} {inj₂ _} → λ _ z → z
            ; {inj₂ _} {inj₁ _} {inj₁ _} → λ _ z → z
            ; {inj₂ _} {inj₁ _} {inj₂ _} → λ _ → λ ()
            ; {inj₂ _} {inj₂ _} {inj₁ _} → λ z _ → z
            ; {inj₂ _} {inj₂ _} {inj₂ _} → D._∘_
            }
  ; id = λ { {inj₁ _} → C.id ; {inj₂ _} → D.id }
  ; assoc = λ { {inj₁ _} {inj₁ _} {inj₁ _} {inj₁ _} → C.assoc
              ; {inj₁ _} {inj₁ _} {inj₁ _} {inj₂ _} → λ {f} {g} → λ {}
              ; {inj₁ _} {inj₁ _} {inj₂ _} {inj₁ _} → λ {f} {g} → λ {}
              ; {inj₁ _} {inj₁ _} {inj₂ _} {inj₂ _} → λ {f} → λ {}
              ; {inj₁ _} {inj₂ _} {inj₁ _} {inj₁ _} → λ {f} → λ {}
              ; {inj₁ _} {inj₂ _} {inj₁ _} {inj₂ _} → λ {f} {g} → λ {}
              ; {inj₁ _} {inj₂ _} {inj₂ _} {inj₁ _} → λ {f} {g} → λ {}
              ; {inj₁ _} {inj₂ _} {inj₂ _} {inj₂ _} → λ {}
              ; {inj₂ _} {inj₁ _} {inj₁ _} {inj₁ _} → λ {}
              ; {inj₂ _} {inj₁ _} {inj₁ _} {inj₂ _} → λ {f} {g} → λ {}
              ; {inj₂ _} {inj₁ _} {inj₂ _} {inj₁ _} → λ {f} {g} → λ {}
              ; {inj₂ _} {inj₁ _} {inj₂ _} {inj₂ _} → λ {f} → λ {}
              ; {inj₂ _} {inj₂ _} {inj₁ _} {inj₁ _} → λ {f} → λ {}
              ; {inj₂ _} {inj₂ _} {inj₁ _} {inj₂ _} → λ {f} {g} → λ {}
              ; {inj₂ _} {inj₂ _} {inj₂ _} {inj₁ _} → λ {f} {g} → λ {}
              ; {inj₂ _} {inj₂ _} {inj₂ _} {inj₂ _} → D.assoc
              }
  ; identityˡ = λ { {inj₁ _} {inj₁ _} → C.identityˡ
                  ; {inj₁ _} {inj₂ _} → λ {}
                  ; {inj₂ _} {inj₁ _} → λ {}
                  ; {inj₂ _} {inj₂ _} → D.identityˡ
                  }
  ; identityʳ = λ { {inj₁ _} {inj₁ _} → C.identityʳ
                  ; {inj₁ _} {inj₂ _} → λ {}
                  ; {inj₂ _} {inj₁ _} → λ {}
                  ; {inj₂ _} {inj₂ _} → D.identityʳ
                  }
  ; equiv = λ { {inj₁ _} {inj₁ _} → C.equiv
              ; {inj₁ _} {inj₂ _} → record { refl = λ {} ; sym = λ {i} → λ {} ; trans = λ {i} {j} → λ {} }
              ; {inj₂ _} {inj₁ _} → record { refl = λ {} ; sym = λ {i} → λ {} ; trans = λ {i} {j} → λ {} }
              ; {inj₂ _} {inj₂ _} → D.equiv
              }
  ; ∘-resp-≡ = λ { {inj₁ _} {inj₁ _} {inj₁ _} → C.∘-resp-≡
                 ; {inj₁ _} {inj₁ _} {inj₂ _} → λ {f} → λ {}
                 ; {inj₁ _} {inj₂ _} {inj₁ _} → λ {f} {h} {g} → λ {}
                 ; {inj₁ _} {inj₂ _} {inj₂ _} → λ {f} {h} {g} → λ {}
                 ; {inj₂ _} {inj₁ _} {inj₁ _} → λ {f} {h} {g} → λ {}
                 ; {inj₂ _} {inj₁ _} {inj₂ _} → λ {f} {h} {g} → λ {}
                 ; {inj₂ _} {inj₂ _} {inj₁ _} → λ {f} → λ {}
                 ; {inj₂ _} {inj₂ _} {inj₂ _} → D.∘-resp-≡
                 }
  }
  where
  module C = Category C
  module D = Category D
