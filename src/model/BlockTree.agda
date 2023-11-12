module BlockTree where

open import Data.Bool using (Bool;true;false;_∧_)
open import Data.List using (List;[];_∷_;_++_)
open import Parameters
open import Block

correctBlock : Block → Bool
correctBlock b = Winner (bid b) (sl b)

all : {A : Set} → (A → Bool) → List A  → Bool
all p [] = true
all p (a ∷ as) = p a ∧ all p as

correctBlocks : Chain → Bool
correctBlocks bs = all correctBlock bs

postulate _==H_ : Hash → Hash → Bool

linked : Block → Block → Bool
linked b b' = pred b ==H HashB b'

postulate _==B_ : Block → Block → Bool

properlyLinked : Chain → Bool
properlyLinked [] = false
properlyLinked (b ∷ []) = b ==B GenesisBlock
properlyLinked (b ∷ b' ∷ bs) = linked b b' ∧ properlyLinked bs

-- ...

postulate decreasingSlots : Chain → Bool

validChain : Chain → Bool
validChain c = correctBlocks c ∧ properlyLinked c ∧ decreasingSlots c

open import Relation.Binary.PropositionalEquality

record BlockTree : Set₁ where
  field T : Set
        extendTree : T → Block → T
        buildTree  : BlockPool → T
        bestChain  : Slot → T → Chain
        allBlocks  : T → BlockPool
        tree0 : T

        -- All blocks contain correct blocks
        prop1 : ∀ bp → allBlocks (buildTree bp) ≡ bp
        prop2 : allBlocks tree0 ≡ GenesisBlock ∷ []
        prop3 : ∀ t b → allBlocks (extendTree t b) ≡ allBlocks t ++ (b ∷ [])
        
        -- Building nothing gives the empty tree
        prop4 : buildTree [] ≡ tree0

        -- Composition of build and extend
        prop5 : ∀ b bp → extendTree (buildTree bp) b ≡ buildTree (b ∷ bp)

        -- Selecting best chain
        prop6 : ∀ t s → validChain (bestChain s t) ≡ true
        -- prop7
        -- prop8
