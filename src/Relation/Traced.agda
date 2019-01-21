open import Polynomial.Simple.AlmostCommutativeRing
open import Relation.Binary
open import Data.Bool using (Bool; false; true ; _∧_; _∨_; not; if_then_else_)

module Relation.Traced
  {c ℓ}
  (base : AlmostCommutativeRing c ℓ)
  (_≟_ : AlmostCommutativeRing.Carrier base → AlmostCommutativeRing.Carrier base → Bool)
  where

open import Data.Sum
open import Relation.Binary.Construct.Closure.Equivalence
open import Relation.Binary.Construct.Closure.Symmetric
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Data.String
open import Relation.Nullary
open import Function
open import Level using (_⊔_)
open import Algebra.FunctionProperties
open import Data.String using (String)
open import Data.String.Unsafe using (_==_)
open import Data.Maybe

open AlmostCommutativeRing base

data Variable : Set c where
  K : Carrier → Variable
  V : String → Variable

data BinOp : Set where
  [+] : BinOp
  [*] : BinOp
  [^] : BinOp

data Step : Set c where
  [sym]      : Step → Step
  [cong]     : Step → BinOp → Step → Step
  [-cong]    : Step → Step
  [refl]     : Variable  → Step
  [assoc]    : BinOp → Variable → Variable → Variable → Step
  [ident]    : BinOp → Variable → Step
  [comm]     : BinOp → Variable → Variable → Step
  [zero]     : Variable → Step
  [distrib]  : Variable → Variable → Variable → Step
  [-distrib] : Variable → Variable → Step
  [-+comm]   : Variable → Variable → Step

record _≈ⁱ_ (x y : Variable) : Set c where
   constructor ~?_
   field
     why : Step
open _≈ⁱ_

eqBinOp : BinOp → BinOp → Bool
eqBinOp [+] [+] = true
eqBinOp [*] [*] = true
eqBinOp [^] [^] = true
eqBinOp _ _ = false

eqVariable : Variable → Variable → Bool
eqVariable (K x) (K y) = x ≟ y
eqVariable (V x) (V y) = x == y
eqVariable _ _ = false

eqStep : (x y : Step) → Bool
eqStep ([sym] x) ([sym] y) = eqStep x y
eqStep ([cong] x x₁ x₂) ([cong] y y₁ y₂) = eqStep x y ∧ eqBinOp x₁ y₁ ∧ eqStep x₂ y₂
eqStep ([-cong] x) ([-cong] y) = eqStep x y
eqStep ([assoc] x x₁ x₂ x₃) ([assoc] y y₁ y₂ y₃) = eqBinOp x y ∧ eqVariable x₁ y₁ ∧ eqVariable x₂ y₂ ∧ eqVariable x₃ y₃
eqStep ([ident] x x₁) ([ident] y y₁) = eqBinOp x y ∧ eqVariable x₁ y₁
eqStep ([comm] x x₁ x₂) ([comm] y y₁ y₂) = eqBinOp x y ∧ eqVariable x₁ y₁ ∧ eqVariable x₂ y₂
eqStep ([zero] x) ([zero] y) = eqVariable x y
eqStep ([distrib] x x₁ x₂) ([distrib] y y₁ y₂) = eqVariable x y ∧ eqVariable x₁ y₁ ∧ eqVariable x₂ y₂
eqStep ([-distrib] x x₁) ([-distrib] y y₁) = eqVariable x y ∧ eqVariable x₁ y₁
eqStep ([-+comm] x x₁) ([-+comm] y y₁) = eqVariable x y ∧ eqVariable x₁ y₁
eqStep ([refl] x) ([refl] y) = eqVariable x y
eqStep _ _ = false

closed : Step → Bool
closed ([sym] x) = closed x
closed ([cong] x x₁ x₂) = closed x ∧ closed x₂
closed ([-cong] x) = closed x
closed ([refl] (K x)) = true
closed ([refl] (V x)) = false
closed ([assoc] x (K x₁) (K x₂) (K x₃)) = true
closed ([assoc] x x₁ x₂ x₃) = false
closed ([ident] x (K x₁)) = true
closed ([ident] x (V x₁)) = false
closed ([comm] x (K x₁) (K x₂)) = true
closed ([comm] x x₁ x₂) = false
closed ([zero] (K x)) = true
closed ([zero] (V x)) = false
closed ([distrib] (K x) (K x₁) (K x₂)) = true
closed ([distrib] x x₁ x₂) = false
closed ([-distrib] (K x) (K x₁)) = true
closed ([-distrib] x x₁) = false
closed ([-+comm] (K x) (K x₁)) = true
closed ([-+comm] x x₁) = false

interesting : Step → Maybe Step
interesting ([sym] x) = interesting x
interesting ([-cong] x) = interesting x
interesting ([refl] x) = nothing
interesting ([assoc] x x₁ x₂ x₃) = nothing
interesting ([ident] x x₁) = nothing
interesting ([zero] x) = nothing
interesting ([cong] x x₁ x₂) with interesting x | interesting x₂
interesting ([cong] x x₁ x₂) | just res₁ | just res₂ = just ([cong] res₁ x₁ res₂)
interesting ([cong] x x₁ x₂) | just res₁ | nothing  = just res₁
interesting ([cong] x x₁ x₂) | nothing | just res₂ = just res₂
interesting ([cong] x x₁ x₂) | nothing | nothing  = nothing
interesting s@([comm] x x₁ x₂) with closed s
interesting s@([comm] x x₁ x₂) | true = nothing
interesting s@([comm] [^] x₁ x₂) | false = nothing
interesting s@([comm] [+] (K x₁) x₂) | false = if (x₁ ≟ 0#) then nothing else just s
interesting s@([comm] [+] x₁ (K x₂)) | false = if (x₂ ≟ 0#) then nothing else just s
interesting s@([comm] [+] x₁ x₂) | false = just ([comm] [+] x₁ x₂)
interesting s@([comm] [*] (K x₁) x₂) | false = if (x₁ ≟ 0# ∨ x₁ ≟ 1#) then nothing else just s
interesting s@([comm] [*] x₁ (K x₂)) | false = if (x₂ ≟ 0# ∨ x₂ ≟ 1#) then nothing else just s
interesting s@([comm] [*] x₁ x₂) | false = just s
interesting s@([distrib] x x₁ x₂) with closed s
interesting s@([distrib] x x₁ x₂) | true = nothing
interesting s@([distrib] (K x) x₁ x₂) | false = if (x ≟ 0# ∨ x ≟ 1#) then nothing else just s
interesting s@([distrib] (V x) x₁ x₂) | false = just s
interesting s@([-distrib] x x₁) = nothing
interesting s@([-+comm] x x₁) = nothing

liftBinOp : (Carrier → Carrier → Carrier) → Variable → Variable → Variable
liftBinOp _f_ (K x) (K y) = K (x f y)
liftBinOp _f_ (K x) (V y) = V y
liftBinOp _f_ (V x) y = V x

liftOp : (Carrier → Carrier) → Variable → Variable
liftOp f (K x) = K (f x)
liftOp f (V x) = V x

neg-cong : ∀ {x y} → x ≈ⁱ y → liftOp -_  x ≈ⁱ liftOp -_  y
neg-cong (~? reason) = ~? ( [-cong] reason)

zip-cong : BinOp
         → (f : Variable → Variable → Variable)
         → Congruent₂ (EqClosure _≈ⁱ_) f
zip-cong op f {x₁} {x₂} {y₁} {y₂} ε ε = ε
zip-cong op f {x₁} {x₂} {y₁} {y₂} ε (inj₁ (~? yr) ◅ ys) = inj₁ (~? ([cong] ([refl] x₁) op yr)) ◅ zip-cong op f ε ys
zip-cong op f {x₁} {x₂} {y₁} {y₂} ε (inj₂ (~? yr) ◅ ys) = inj₂ (~? ([cong] ([refl] x₁) op yr)) ◅ zip-cong op f ε ys
zip-cong op f {x₁} {x₂} {y₁} {y₂} (inj₁ (~? xr) ◅ xs) ε = inj₁ (~? ([cong] xr op ([refl] y₁))) ◅ zip-cong op f xs ε
zip-cong op f {x₁} {x₂} {y₁} {y₂} (inj₂ (~? xr) ◅ xs) ε = inj₂ (~? ([cong] xr op ([refl] y₁))) ◅ zip-cong op f xs ε
zip-cong op f {x₁} {x₂} {y₁} {y₂} (inj₁ (~? xr) ◅ xs) (inj₁ (~? yr) ◅ ys) = inj₁ (~? ([cong] xr op yr)) ◅ zip-cong op f xs ys
zip-cong op f {x₁} {x₂} {y₁} {y₂} (inj₁ (~? xr) ◅ xs) (inj₂ (~? yr) ◅ ys) = inj₁ (~? ([cong] xr op ([sym] yr))) ◅ zip-cong op f xs ys
zip-cong op f {x₁} {x₂} {y₁} {y₂} (inj₂ (~? xr) ◅ xs) (inj₁ (~? yr) ◅ ys) = inj₂ (~? ([cong] xr op ([sym] yr))) ◅ zip-cong op f xs ys
zip-cong op f {x₁} {x₂} {y₁} {y₂} (inj₂ (~? xr) ◅ xs) (inj₂ (~? yr) ◅ ys) = inj₂ (~? ([cong] xr op yr)) ◅ zip-cong op f xs ys

isZero : (x : Variable) → Maybe (EqClosure _≈ⁱ_ (K 0#) x)
isZero (V x) = nothing
isZero (K x) with 0≟ x
isZero (K x) | just x₁ = just (inj₁ (~? [refl] (K x)) ◅ ε)
isZero (K x) | nothing = nothing

tracedRing : AlmostCommutativeRing c c
tracedRing = record
  { Carrier                 = Variable
  ; _≈_                     = EqClosure _≈ⁱ_
  ; _+_                     = liftBinOp _+_
  ; _*_                     = liftBinOp _*_
  ; -_                      = liftOp -_
  ; 0#                      = K 0#
  ; 1#                      = K 1#
  ; 0≟_                     = isZero
  ; isAlmostCommutativeRing = record
    {  -‿cong      = Relation.Binary.Construct.Closure.ReflexiveTransitive.gmap (liftOp -_ ) (Data.Sum.map neg-cong neg-cong)
    ; -‿*-distribˡ = λ x y → return (inj₁ (~? [-distrib] x y))
    ; -‿+-comm     = λ x y → return (inj₁ (~? [-+comm] x y))
    ; isCommutativeSemiring = record
      { distribʳ = λ x y z → return (inj₁ (~? [distrib] x y z))
      ; zeroˡ = λ x → return (inj₁ (~? ([zero] x)))
      ; *-isCommutativeMonoid = record
        { identityˡ = λ x → return (inj₁ (~? [ident] [*] x))
        ; comm = λ x y → return (inj₁ (~? [comm] [*] x y))
        ; isSemigroup = record
          { assoc = λ x y z → return (inj₁ (~? [assoc] [*] x y z))
          ; isMagma = record
            { isEquivalence = Relation.Binary.Construct.Closure.Equivalence.isEquivalence _≈ⁱ_
            ; ∙-cong = zip-cong [*] (liftBinOp _*_)
            }
          }
        }
      ; +-isCommutativeMonoid = record
        { identityˡ = λ x → return (inj₁ (~? ([ident] [+] x)))
        ; comm = λ x y → return (inj₁ (~? ([comm] [+] x y)))
        ; isSemigroup = record
          { assoc = λ x y z → return (inj₁ (~? ([assoc] [+] x y z)))
          ; isMagma = record
            { isEquivalence = Relation.Binary.Construct.Closure.Equivalence.isEquivalence _≈ⁱ_
            ; ∙-cong = zip-cong [+] (liftBinOp _+_)
            }
          }
        }
      }
    }
  }

open import Data.List as List

showProof′ : ∀ {x y} → EqClosure _≈ⁱ_ x y → List Step
showProof′ ε = []
showProof′ (inj₁ x ◅ xs) = why x ∷ showProof′ xs
showProof′ (inj₂ y ◅ xs) = why y ∷ showProof′ xs

compressProof : List Step → List Step
compressProof [] = []
compressProof (x ∷ xs) = go [] x xs
  where
  go : List Step → Step → List Step → List Step
  go ys y [] = List.reverse (y ∷ ys)
  go ys y (x ∷ xs) with eqStep y x
  go ys y (x ∷ xs) | false = go (y ∷ ys) x xs
  go [] y (x ∷ []) | true = []
  go [] y (x ∷ x₁ ∷ xs) | true = go [] x₁ xs
  go (x₁ ∷ ys) y (x ∷ xs) | true = go ys x₁ xs

showProof : ∀ {x y} → EqClosure _≈ⁱ_ x y → List Step
showProof = List.foldr spotReverse [] ∘ List.mapMaybe interesting ∘ compressProof ∘ showProof′
  where
  spotReverse : Step → List Step → List Step
  spotReverse z@([comm] op x y) zs@([comm] op′ x′ y′ ∷ xs) = if eqBinOp op op′ ∧ eqVariable x y′ ∧ eqVariable y x′ then xs else z ∷ zs
  spotReverse x xs = x ∷ xs
