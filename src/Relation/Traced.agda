open import Polynomial.Simple.AlmostCommutativeRing

module Relation.Traced {c ℓ} (base : AlmostCommutativeRing c ℓ) where

open import Data.Sum
open import Relation.Binary.Construct.Closure.Equivalence
open import Relation.Binary.Construct.Closure.Symmetric
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Data.String
open import Relation.Nullary
open import Function
open import Level using (_⊔_)
open import Algebra.FunctionProperties

open AlmostCommutativeRing

record _≈ⁱ_ (x y : base .Carrier) : Set ℓ where
   constructor _~?_
   field
     proof : base ._≈_ x y
     why : String

open _≈ⁱ_

decTrace : ∀ x y → Dec (EqClosure _≈ⁱ_ x y)
decTrace x y with base ._≟_ x y
decTrace x y | yes p = yes (return (inj₁ (p ~? "refl")))
decTrace x y | no ¬p = no (¬p ∘ gfold id (base ._≈_) (trans base ∘ [ id , sym base ] ∘ Data.Sum.map proof proof) (refl base))

neg-cong : ∀ {x y} → x ≈ⁱ y → -_ base x ≈ⁱ -_ base y
neg-cong (prf ~? reason) = -‿cong base prf ~? ( "-(" ++ reason ++ ")")

right-cong : ∀ {x y} {f : Carrier base → Carrier base} → String → Congruent₁ (_≈_ base) f → x ≈ⁱ y → f x ≈ⁱ f y
right-cong op f-cong (p ~? r) = f-cong p ~? ("_" ++ op ++ "(" ++ r ++ ")")

left-cong : ∀ {x y} {f : Carrier base → Carrier base} → String → Congruent₁ (_≈_ base) f → x ≈ⁱ y → f x ≈ⁱ f y
left-cong op f-cong (p ~? r) = f-cong p ~? ("(" ++ r ++ ")" ++ op ++ "_")

zip-cong : String
         → ∀ {f : Carrier base → Carrier base → Carrier base}
         → Congruent₂ (_≈_ base) f
         → Congruent₂ (EqClosure _≈ⁱ_) f
zip-cong op f-cong ε ε = ε
zip-cong op {f} f-cong ε (y ◅ ys) = Relation.Binary.Construct.Closure.ReflexiveTransitive.gmap (f _) (Data.Sum.map (right-cong op (f-cong (refl base))) (right-cong op (f-cong (refl base)))) (y ◅ ys)
zip-cong op {f} f-cong (x ◅ xs) ε = Relation.Binary.Construct.Closure.ReflexiveTransitive.gmap (λ x → f x _) (Data.Sum.map (left-cong op (λ p → f-cong p (refl base))) (left-cong op (λ p → f-cong p (refl base)))) (x ◅ xs)
zip-cong op f-cong (inj₁ (x ~? xr) ◅ xs) (inj₁ (y ~? yr) ◅ ys) = inj₁ (f-cong x y ~? (xr ++ op ++ yr)) ◅ zip-cong op f-cong xs ys
zip-cong op f-cong (inj₁ (x ~? xr) ◅ xs) (inj₂ (y ~? yr) ◅ ys) = inj₁ (f-cong x (sym base y) ~? (xr ++ op ++ "sym(" ++ yr ++ ")")) ◅ zip-cong op f-cong xs ys
zip-cong op f-cong (inj₂ (x ~? xr) ◅ xs) (inj₁ (y ~? yr) ◅ ys) = inj₂ (f-cong x (sym base y) ~? (xr ++ op ++ "sym(" ++ yr ++ ")")) ◅ zip-cong op f-cong xs ys
zip-cong op f-cong (inj₂ (x ~? xr) ◅ xs) (inj₂ (y ~? yr) ◅ ys) = inj₂ (f-cong x y ~? (xr ++ op ++ yr)) ◅ zip-cong op f-cong xs ys

tracedRing : AlmostCommutativeRing c (c ⊔ ℓ)
tracedRing = record
  { Carrier                 = base .Carrier
  ; _≈_                     = EqClosure _≈ⁱ_
  ; _≟_                     = decTrace
  ; _+_                     = _+_ base
  ; _*_                     = _*_ base
  ; -_                      = -_ base
  ; 0#                      = 0# base
  ; 1#                      = 1# base
  ; isAlmostCommutativeRing = record
    {  -‿cong      = Relation.Binary.Construct.Closure.ReflexiveTransitive.gmap (-_ base) (Data.Sum.map neg-cong neg-cong)
    ; -‿*-distribˡ = λ x y → return (inj₁ (-‿*-distribˡ base x y ~? "-‿distribˡ"))
    ; -‿+-comm     = λ x y → return (inj₁ (-‿+-comm     base x y ~? "-‿+-comm"))
    ; isCommutativeSemiring = record
      { distribʳ = λ x y z → return (inj₁ (distribʳ base x y z ~? "distribʳ"))
      ; zeroˡ = λ x → return (inj₁ (zeroˡ base x ~? "zeroˡ"))
      ; *-isCommutativeMonoid = record
        { identityˡ = λ x → return (inj₁ (*-identityˡ base x ~? "*-identityˡ"))
        ; comm = λ x y → return (inj₁ (*-comm base x y ~? "*-comm"))
        ; isSemigroup = record
          { assoc = λ x y z → return (inj₁ (*-assoc base x y z ~? "*-assoc"))
          ; isMagma = record
            { isEquivalence = Relation.Binary.Construct.Closure.Equivalence.isEquivalence _≈ⁱ_
            ; ∙-cong = zip-cong "*" (*-cong base)
            }
          }
        }
      ; +-isCommutativeMonoid = record
        { identityˡ = λ x → return (inj₁ (+-identityˡ base x ~? "+-identityˡ"))
        ; comm = λ x y → return (inj₁ (+-comm base x y ~? "+-comm"))
        ; isSemigroup = record
          { assoc = λ x y z → return (inj₁ (+-assoc base x y z ~? "+-assoc"))
          ; isMagma = record
            { isEquivalence = Relation.Binary.Construct.Closure.Equivalence.isEquivalence _≈ⁱ_
            ; ∙-cong = zip-cong "+" (+-cong base)
            }
          }
        }
      }
    }
  }

open import Data.List

showProof : ∀ {x y} → EqClosure _≈ⁱ_ x y → List String
showProof ε = []
showProof (inj₁ x ◅ xs) = why x ∷ showProof xs
showProof (inj₂ y ◅ xs) = why y ∷ showProof xs
