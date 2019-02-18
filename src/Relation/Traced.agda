{-# OPTIONS --without-K --safe #-}

open import Polynomial.Simple.AlmostCommutativeRing
open import Relation.Binary
open import Data.Bool using (Bool; false; true ; _∧_; _∨_; not; if_then_else_)
open import Data.String using (String)
open import EqBool

module Relation.Traced
  {c ℓ}
  (base : AlmostCommutativeRing c ℓ)
  ⦃ eqBase : HasEqBool (AlmostCommutativeRing.Carrier base) ⦄
  (showBase : AlmostCommutativeRing.Carrier base → String)
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
open import Data.String.Unsafe renaming (_==_ to eqBoolString)
open import Data.Maybe
open import Data.Nat using (ℕ)


open AlmostCommutativeRing base
open import Polynomial.Expr.Normalising rawRing showBase

open import Agda.Builtin.FromNat using (Number; fromNat) public

instance
  numberVar : {{nc : Number Carrier}} → Number Expr
  numberVar {{nc}} = record
    { Constraint = Number.Constraint nc
    ; fromNat = λ n → C ( (Number.fromNat nc n)) }

data BinOp : Set where
  [+] : BinOp
  [*] : BinOp

instance
  eqBinOp : HasEqBool BinOp
  _==_ ⦃ eqBinOp ⦄ [+] [+] = true
  _==_ ⦃ eqBinOp ⦄ [+] [*] = false
  _==_ ⦃ eqBinOp ⦄ [*] [+] = false
  _==_ ⦃ eqBinOp ⦄ [*] [*] = true

liftBinOp : BinOp → Expr → Expr → Expr
liftBinOp [+] (C x) (C y) = normalise (C (x + y))
liftBinOp [+] (C x) (O y) = normalise (O (K x ⊕ y))
liftBinOp [+] (O x) (C y) = normalise (O (x ⊕ K y))
liftBinOp [+] (O x) (O y) = normalise (O (x ⊕ y))
liftBinOp [*] (C x) (C y) = normalise (C (x * y))
liftBinOp [*] (C x) (O y) = normalise (O (K x ⊗ y))
liftBinOp [*] (O x) (C y) = normalise (O (x ⊗ K y))
liftBinOp [*] (O x) (O y) = normalise (O (x ⊗ y))

⊟_ : Expr → Expr
⊟ C x = C (- x)
⊟ O x = normalise (O (⊝ x))

data Step : Set c where
  [sym]      : Step → Step
  [cong]     : Step → BinOp → Step → Step
  [-cong]    : Step → Step
  [refl]     : Expr  → Step
  [assoc]    : BinOp → Expr → Expr → Expr → Step
  [ident]    : BinOp → Expr → Step
  [comm]     : BinOp → Expr → Expr → Step
  [zero]     : Expr → Step
  [distrib]  : Expr → Expr → Expr → Step
  [-distrib] : Expr → Expr → Step
  [-+comm]   : Expr → Expr → Step

_==S_ : Step → Step → Bool
_==S_ ([sym] x) ([sym] y) = x ==S y
_==S_ ([cong] x x₁ x₂) ([cong] y y₁ y₂) = x ==S y ∧ x₁ == y₁ ∧ x₂ ==S y₂
_==S_ ([-cong] x) ([-cong] y) = x ==S y
_==S_ ([assoc] x x₁ x₂ x₃) ([assoc] y y₁ y₂ y₃) = x == y ∧ x₁ == y₁ ∧ x₂ == y₂ ∧ x₃ == y₃
_==S_ ([ident] x x₁) ([ident] y y₁) = x == y ∧ x₁ == y₁
_==S_ ([comm] x x₁ x₂) ([comm] y y₁ y₂) = x == y ∧ x₁ == y₁ ∧ x₂ == y₂
_==S_ ([zero] x) ([zero] y) = x == y
_==S_ ([distrib] x x₁ x₂) ([distrib] y y₁ y₂) = x == y ∧ x₁ == y₁ ∧ x₂ == y₂
_==S_ ([-distrib] x x₁) ([-distrib] y y₁) = x == y ∧ x₁ == y₁
_==S_ ([-+comm] x x₁) ([-+comm] y y₁) = x == y ∧ x₁ == y₁
_==S_ ([refl] x) ([refl] y) = x == y
_==S_ _ _ = false

instance
  eqStep : HasEqBool Step
  _==_ {{eqStep}} = _==S_

record _≈ⁱ_ (x y : Expr) : Set c where
   constructor ~?_
   field
     why : Step
open _≈ⁱ_


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
interesting s@([comm] _ x y) with x == y
interesting s@([comm] _ x y) | true = nothing
interesting s@([comm] o (C x) (C y))    | false = nothing
interesting s@([comm] [+] (C x) x₂)     | false = if x == 0# then nothing else just s
interesting s@([comm] [+] (O x) (C x₁)) | false = if x₁ == 0# then nothing else just s
interesting s@([comm] [+] (O x) (O x₁)) | false = just s
interesting s@([comm] [*] (C x) x₂)     | false = if (x == 0# ∨ x == 1#) then nothing else just s
interesting s@([comm] [*] (O x) (C x₁)) | false = if (x₁ == 0# ∨ x₁ == 1#) then nothing else just s
interesting s@([comm] [*] (O x) (O x₁)) | false = just s
interesting s@([distrib] (C _) (C _) (C _)) = nothing
interesting s@([distrib] (C x) x₁ x₂) = if (x == 0# ∨ x == 1#) then nothing else just s
interesting s@([distrib] x x₁ x₂) = just s
interesting s@([-distrib] x x₁) = nothing
interesting s@([-+comm] x x₁) = nothing

neg-cong : ∀ {x y} → x ≈ⁱ y → ⊟_  x ≈ⁱ ⊟_  y
neg-cong (~? reason) = ~? ( [-cong] reason)

zip-cong : BinOp
         → (f : Expr → Expr → Expr)
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

isZero : (x : Expr) → Maybe (EqClosure _≈ⁱ_ (C 0#) x)
isZero (C x) = if 0# == x then just (inj₁ (~? [refl] (C x)) ◅ ε) else nothing
isZero _ = nothing

tracedRing : AlmostCommutativeRing c c
tracedRing = record
  { Carrier                 = Expr
  ; _≈_                     = EqClosure _≈ⁱ_
  ; _+_                     = liftBinOp [+]
  ; _*_                     = liftBinOp [*]
  ; -_                      = ⊟_
  ; 0#                      = C 0#
  ; 1#                      = C 1#
  ; 0≟_                     = isZero
  ; isAlmostCommutativeRing = record
    {  -‿cong      = Relation.Binary.Construct.Closure.ReflexiveTransitive.gmap ⊟_ (Data.Sum.map neg-cong neg-cong)
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
            ; ∙-cong = zip-cong [*] (liftBinOp [*])
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
            ; ∙-cong = zip-cong [+] (liftBinOp [+])
            }
          }
        }
      }
    }
  }

open import Data.List as List using (List; _∷_; [])

record Explanation {a} (A : Set a) : Set (a ⊔ c) where
  constructor _≈⟨_⟩≈_
  field
    lhs : A
    step : Step
    rhs : A
open Explanation

toExplanation : ∀ {x y} → x ≈ⁱ y → Explanation Expr
toExplanation {x} {y} x≈y = x ≈⟨ why x≈y ⟩≈ y

showProof′ : ∀ {x y} → EqClosure _≈ⁱ_ x y → List (Explanation Expr)
showProof′ ε = []
showProof′ (inj₁ x ◅ xs) = toExplanation x ∷ showProof′ xs
showProof′ (inj₂ y ◅ xs) = toExplanation y ∷ showProof′ xs

open import Data.String.Printf
open Printf standard

⟨_⟩ₛ : Step → String
⟨ [sym] x  ⟩ₛ             = printf "sym (%s)" ⟨ x ⟩ₛ
⟨ [cong] x [+] x₂ ⟩ₛ      = printf "(%s) + (%s)" ⟨ x ⟩ₛ ⟨ x₂ ⟩ₛ
⟨ [cong] x [*] x₂ ⟩ₛ      = printf "(%s) * (%s)" ⟨ x ⟩ₛ ⟨ x₂ ⟩ₛ
⟨ [-cong] x ⟩ₛ            = printf "- (%s)" ⟨ x ⟩ₛ
⟨ [refl] x ⟩ₛ             = "eval"
⟨ [assoc] [+] x₁ x₂ x₃ ⟩ₛ = printf "+-assoc(%s, %s, %s)" ⟨ x₁ ⟩ₑ  ⟨ x₂ ⟩ₑ ⟨ x₃ ⟩ₑ
⟨ [assoc] [*] x₁ x₂ x₃ ⟩ₛ = printf "*-assoc(%s, %s, %s)" ⟨ x₁ ⟩ₑ  ⟨ x₂ ⟩ₑ ⟨ x₃ ⟩ₑ
⟨ [ident] [+] x₁ ⟩ₛ       = printf "+-ident(%s)" ⟨ x₁ ⟩ₑ
⟨ [ident] [*] x₁ ⟩ₛ       = printf "*-ident(%s)" ⟨ x₁ ⟩ₑ
⟨ [comm] [+] x₁ x₂ ⟩ₛ     = printf "+-comm(%s, %s)" ⟨ x₁ ⟩ₑ ⟨ x₂ ⟩ₑ
⟨ [comm] [*] x₁ x₂ ⟩ₛ     = printf "*-comm(%s, %s)" ⟨ x₁ ⟩ₑ ⟨ x₂ ⟩ₑ
⟨ [zero] x ⟩ₛ             = printf "*-zero(%s)" ⟨ x ⟩ₑ
⟨ [distrib] x x₁ x₂ ⟩ₛ    = printf "*-distrib(%s, %s, %s)" ⟨ x ⟩ₑ ⟨ x₁ ⟩ₑ  ⟨ x₂ ⟩ₑ
⟨ [-distrib] x x₁ ⟩ₛ      = printf "-‿distrib(%s, %s)" ⟨ x ⟩ₑ ⟨ x₁ ⟩ₑ
⟨ [-+comm] x x₁ ⟩ₛ        = printf "-+-comm(%s, %s)" ⟨ x ⟩ₑ ⟨ x₁ ⟩ₑ

open import Data.Product as Prod
open import Agda.Builtin.Nat using (_<_)

Distances : Set c
Distances = List (Explanation Expr × ℕ)

addNew : Explanation Expr × ℕ → Distances → Distances
addNew (e , d) [] = []
addNew (e , d) ((x , xd) ∷ xs) = if rhs e == rhs x then if xd < d then ((x , xd) ∷ xs) else ((e , d) ∷ xs) else (x , xd) ∷ (addNew (e , d) xs)

withInds : ∀ {a} {A : Set a} → List A → List (A × ℕ)
withInds xs = List.foldr (λ x xs n → (x , n) ∷ xs (ℕ.suc n)) (const []) xs ℕ.zero

shorten : List (Explanation Expr) → List (Explanation Expr)
shorten [] = []
shorten xs@(y ∷ ys) = List.reverse (reconstruct (last′ y ys) (Vec.fromList (List.map proj₁ (List.foldr addNew [] (withInds xs)))))
  where
  open import Data.Vec as Vec using (Vec; _∷_; [])

  last′ : ∀ {a} {A : Set a} → A → List A → A
  last′ x [] = x
  last′ _ (x ∷ xs) = last′ x xs

  pop : ∀ {n a} {A : Set a} → (A → Bool) → Vec A (ℕ.suc n) → Maybe (A × Vec A n)
  pop p (x ∷ xs) with p x
  pop p (x ∷ []) | false = nothing
  pop p (x₁ ∷ x₂ ∷ xs) | false = Data.Maybe.map (Prod.map₂ (x₁ ∷_)) (pop p (x₂ ∷ xs))
  pop p (x ∷ xs) | true = just (x , xs)

  reconstruct : ∀ {n} → Explanation Expr → Vec (Explanation Expr) n → List (Explanation Expr)
  reconstruct e [] = e ∷ []
  reconstruct e xs@(_ ∷ _) with pop (λ x → rhs x == lhs e) xs
  reconstruct e (_ ∷ _) | just (y , ys) = e ∷ reconstruct y ys
  reconstruct e (_ ∷ _) | nothing = e ∷ []


showProof : ∀ {x y} → EqClosure _≈ⁱ_ x y → List String
showProof {x} {y} pr = start ∘ List.foldr unparse [] ∘ shorten ∘ List.mapMaybe interesting′ $ steps
  where
  steps : List (Explanation Expr)
  steps = showProof′ pr

  start : List String → List String
  start [] = []
  start p@(s ∷ _) = if s == x′ then p else x′ ∷ "    ={ eval }" ∷ p
    where
    x′ = ⟨ x ⟩ₑ

  unparse : Explanation Expr → List String → List String
  unparse (lhs₁ ≈⟨ step₁ ⟩≈ rhs₁) [] = if r′ == r then l ∷ m ∷ r ∷ [] else l ∷ m ∷ r ∷ "    ={ eval }" ∷ r′ ∷ []
    where
    l = ⟨ lhs₁ ⟩ₑ
    m = printf "    ={ %s }" ⟨ step₁ ⟩ₛ
    r′ = ⟨ y ⟩ₑ
    r = ⟨ rhs₁ ⟩ₑ
  unparse (lhs₁ ≈⟨ step₁ ⟩≈ rhs₁) (y ∷ ys) = if r == y then l ∷ m ∷ y ∷ ys else l ∷ m ∷ r ∷ "    ={ eval }" ∷ y ∷ ys
    where
    l = ⟨ lhs₁ ⟩ₑ
    m = printf "    ={ %s }" ⟨ step₁ ⟩ₛ
    r = ⟨ rhs₁ ⟩ₑ

  interesting′ : Explanation Expr → Maybe (Explanation Expr)
  interesting′ = just
  -- interesting′ (lhs ≈⟨ stp ⟩≈ rhs) with interesting stp
  -- interesting′ (lhs ≈⟨ stp ⟩≈ rhs) | just x = just (lhs ≈⟨ x ⟩≈ rhs)
  -- interesting′ (lhs ≈⟨ stp ⟩≈ rhs) | nothing = nothing

open import Agda.Builtin.FromString using (IsString; fromString) public
import Data.String.Literals
open import Data.Unit using (⊤)
open import Level using (Lift)

instance
  stringString : IsString String
  stringString = Data.String.Literals.isString

instance
  exprString : IsString Expr
  exprString = record
    { Constraint = λ _ → Lift _ ⊤ ; fromString = λ s → O (V s) }
