module Positional.PAdic.Models where

open import Data.Product
open import Function
open import Positional.PAdic
open Interval
open import Level using (_⊔_)

open import Data.Nat as ℕ using (ℕ; suc; zero)

record Model {s} (Symbol : Set s) (n : ℕ) : Set s where
  coinductive
  field
    encode : Symbol → Interval n → Interval n × Model Symbol n
    decode : Interval n → Symbol × Interval n × Model Symbol n
open Model
open import Relation.Binary
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

module Huffman {k r} (Key : Set k) {_<_ : Rel Key r} (isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_) where
  open import Data.List as List using (List; _∷_; [])
  open import Data.Bool as Bool using (Bool; true; false; if_then_else_)
  open import Data.Maybe

  module Building where
    open import Data.AVL isStrictTotalOrder public
    import Data.AVL.Indexed Key isStrictTotalOrder as Indexed
    open IsStrictTotalOrder isStrictTotalOrder

    freqs : List Key → Tree (const ℕ)
    freqs = List.foldr (λ x xs → insertWith x 1 ℕ._+_ xs) empty

    data HuffTree : Set k where
      leaf : Key → HuffTree
      node : HuffTree → HuffTree → HuffTree

    infixr 5 _&_,_∷_
    data Ordered (n : ℕ) : ℕ → Set k where
      nil : Ordered n 0
      _&_,_∷_ : ∀ {s} → HuffTree → (m : ℕ) → (n≤m : n ℕ.≤ m) → Ordered m s → Ordered n (suc s)

    import Data.Nat.Properties as Prop
    open import Data.Sum

    insertOrdered : ∀ {n s} → HuffTree → (m : ℕ) → (n≤m : n ℕ.≤ m) → Ordered n s → Ordered n (suc s)
    insertOrdered x m n≤m nil = x & m , n≤m ∷ nil
    insertOrdered x m n≤m (x₁ & m₁ , n≤m₁ ∷ xs) with Prop.≤-total m m₁
    insertOrdered x m n≤m (x₁ & m₁ , n≤m₁ ∷ xs) | inj₁ x₂ = x & m , n≤m ∷ x₁ & m₁ , x₂ ∷ xs
    insertOrdered x m n≤m (x₁ & m₁ , n≤m₁ ∷ xs) | inj₂ y = x₁ & m₁ , n≤m₁ ∷ insertOrdered x m y xs

    prune : ∀ {n m} → Ordered m (suc n) → HuffTree
    prune (x & m , n≤m ∷ nil) = x
    prune (x & m , n≤m ∷ x₁ & m₁ , n≤m₁ ∷ xs) = prune (insertOrdered (node x x₁) (m ℕ.+ m₁) (Prop.n≤m+n _ _) xs)


    toOrdered : Tree (const ℕ) → Σ ℕ (Ordered 0)
    toOrdered = List.foldr f (0 , nil) ∘ toList
      where
      f : Key × ℕ → Σ ℕ (Ordered 0) → Σ ℕ (Ordered 0)
      f (x , i) (_ , xs) = _ , insertOrdered (leaf x) i ℕ.z≤n xs


    buildHuffTree : Key × List Key → HuffTree
    buildHuffTree (x , xs) with toOrdered (freqs (x ∷ xs))
    buildHuffTree (x , xs) | zero , snd = prune (leaf x & 1 , ℕ.z≤n ∷ nil)
    buildHuffTree (x , xs) | suc fst , snd = prune snd


    toTable : HuffTree → Tree (const (List Bool))
    toTable = go id
      where
      go : (List Bool → List Bool) → HuffTree → Tree (const (List Bool))
      go k (leaf x) = singleton x (k [])
      go k (node l r) = union (go (k ∘ (false ∷_)) l) (go (k ∘ (true ∷_)) r)

  -- open Building public using (huffEncode)

  open Model
  huffman : Key × List Key → Model Key 1
  huffman xs = go
    where
    tr : Building.HuffTree
    tr = Building.buildHuffTree xs

    mp : Building.Tree (const (List Bool))
    mp = Building.toTable tr

    open import Modular

    one : Mod 1
    one = [ _ ∣ s≥m m≥m ]

    zer : Mod 1
    zer = [ _ ∣ m≥m ]

    lk : Key → Interval 1
    lk x with Building.lookup x mp
    lk x | just x₁ = List.map (λ b → if b then one , one else zer , zer) x₁
    lk x | nothing = []

    gt : Building.HuffTree → Interval 1 → Key × Interval 1
    gt (Building.leaf x) int = x , int
    gt (Building.node l r) [] = proj₁ xs , []
    gt (Building.node l r) (([ .1 ∣ m≥m ] , snd) ∷ int) = gt l int
    gt (Building.node l r) (([ d ∣ s≥m p≥d ] , snd) ∷ int) = gt r int

    go : Model Key 1
    encode go x int = int List.++ lk x , go
    decode go x with gt tr x
    decode go x | fst , snd = fst , snd , go

module Example where
  import Data.Nat.Properties as Prop

  open Huffman ℕ Prop.<-isStrictTotalOrder
  open import Data.List as List using (List; _∷_; [])

  alphabet : List ℕ
  alphabet = 3 ∷ 3 ∷ 2 ∷ 1 ∷ 0 ∷ []

  coder : Model ℕ 1
  coder = huffman (0 , alphabet)

  ex : proj₁ (decode coder (proj₁ (encode coder 3 []))) ≡ 3
  ex = refl
