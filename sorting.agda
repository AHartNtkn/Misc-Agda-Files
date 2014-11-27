module sorting where

open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary
open import Function
open import Data.Product
open import Data.Sum
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Data.List

-- ============ SortedList definition and Insertion Sort implementation, modified from http://web.student.chalmers.se/groups/datx02-dtp/html/SortedList.html =============

mutual
 data SortedList (TO : TotalOrder _ lzero _) : Set where
  []  : SortedList TO
  cons : ∀ a (ls : SortedList TO) → a ≤L ls → SortedList TO

 data _≤L_ {TO} (a : TotalOrder.Carrier TO) : SortedList TO → Set where
  tt : a ≤L []
  _,_  : ∀ {x}{xs}{p} → TotalOrder._≤_ TO a x → a ≤L xs → a ≤L (cons x xs p)

{- equivalent definition
 _≤L_ : ∀ {TO} → TotalOrder.Carrier TO → SortedList TO → Set
 a ≤L [] = ⊤
 _≤L_ {TO} a (cons x xs _) = (TotalOrder._≤_ TO a x) × (a ≤L xs)
-}

ForgetSorting : ∀ {TO} → SortedList TO → List $ TotalOrder.Carrier TO
ForgetSorting [] = []
ForgetSorting (cons a s x) = a ∷ ForgetSorting s

lemma₁ : ∀ {TO} a x (xs : SortedList TO) → TotalOrder._≤_ TO a x → x ≤L xs → a ≤L xs
lemma₁ _ _ [] _ _ = tt 
lemma₁ {TO} a x (cons y xs y≤Lxs) a≤x (x≤y , x≤Lxs) = TotalOrder.trans TO a≤x x≤y , lemma₁ a x xs a≤x x≤Lxs

mutual
 sinsert : ∀ {TO} a → SortedList TO → SortedList TO
 sinsert a [] = cons a [] tt
 sinsert {TO} a (cons x xs x≤Lxs) with TotalOrder.total TO a x
 ... | inj₁ a≤x = cons a (cons x xs x≤Lxs) (a≤x , lemma₁ a x xs a≤x x≤Lxs)
 ... | inj₂ x≤a = cons x (sinsert a xs) (lemma₂ a x xs x≤a x≤Lxs)

 lemma₂ : ∀ {TO} a x → (xs : SortedList TO) → (TotalOrder._≤_ TO x a) → x ≤L xs → x ≤L sinsert a xs
 lemma₂ _ _ [] x≤a _ = x≤a , tt
 lemma₂ {TO} a x (cons y xs y≤Lxs) x≤a (x≤y , x≤Lxs) with TotalOrder.total TO a y
 ... | inj₁ a≤y = x≤a , x≤y , x≤Lxs
 ... | inj₂ y≤a = x≤y , lemma₂ a x xs x≤a x≤Lxs

InsertionSort : ∀ {TO} → List $ TotalOrder.Carrier TO → SortedList TO
InsertionSort = foldr sinsert []

-- To test, run: iSort {ℕTO} SomeNats
iSort : ∀ {TO} → List $ TotalOrder.Carrier TO → List $ TotalOrder.Carrier TO
iSort {TO} = ForgetSorting {TO} ∘ InsertionSort



-- ========= Merge Sort Implementation ========
lemma₃ : ∀ {TO} a b (xs : SortedList TO) → (TotalOrder._≤_ TO a b) → ∀ p → a ≤L (cons b xs p)
lemma₃ a b xs p1 p2 = p1 , lemma₁ a b xs p1 p2

mutual
 merge : ∀ {TO} → SortedList TO → SortedList TO → SortedList TO
 merge [] [] = []
 merge [] (cons a l2 x) = cons a l2 x
 merge (cons a l1 x) [] = cons a l1 x
 merge {TO} (cons a l1 x) (cons b l2 y) with TotalOrder.total TO a b
 ... | inj₁ a≤b = cons a (merge l1 (cons b l2 y)) (lemmaₘ a l1 (cons b l2 y) x (lemma₃ a b l2 a≤b y))
 ... | inj₂ b≤a = cons b (merge (cons a l1 x) l2) (lemmaₘ b (cons a l1 x) l2 (lemma₃ b a l1 b≤a x) y)

 lemmaₘ : ∀ {TO} a (l1 l2 : SortedList TO) → a ≤L l1 → a ≤L l2 → a ≤L merge l1 l2
 lemmaₘ a [] [] _ _ = tt
 lemmaₘ a [] (cons a₁ l2 x) _ p2 = p2
 lemmaₘ a (cons a₁ l1 x) [] p1 _ = p1
 lemmaₘ {TO} a (cons a₁ l1 x) (cons a₂ l2 y) (a≤a₁ , a≤l1) (a≤a₂ , a≤l2) with TotalOrder.total TO a₁ a₂
 ... | inj₁ a₁≤a₂ = a≤a₁ , lemmaₘ a l1 (cons a₂ l2 y) a≤l1 (a≤a₂ , a≤l2)
 ... | inj₂ a₁≥a₂ = a≤a₂ , lemmaₘ a (cons a₁ l1 x) l2 (a≤a₁ , a≤l1) a≤l2

splitList : ∀ {l} {A : Set l} → List A → List A × List A
splitList l = take (⌊ length l /2⌋) l , drop (⌊ length l /2⌋) l

{-# NON_TERMINATING #-}
mergeSort : ∀ {TO} → List $ TotalOrder.Carrier TO → SortedList TO
mergeSort [] = []
mergeSort (x ∷ []) = cons x [] tt
mergeSort (x ∷ y ∷ l) with splitList (x ∷ y ∷ l)
... | l1 , l2 = merge (mergeSort l1) (mergeSort l2)

-- To test, run: mSort {ℕTO} SomeNats
mSort : ∀ {TO} → List $ TotalOrder.Carrier TO → List $ TotalOrder.Carrier TO
mSort {TO} = ForgetSorting {TO} ∘ mergeSort


-- ============ Alternative Merge Sort =============
mergePrep : ∀ {TO} → List $ TotalOrder.Carrier TO → List $ SortedList TO
mergePrep [] = []
mergePrep (x ∷ l) = (cons x [] tt) ∷ mergePrep l

{-# NON_TERMINATING #-}
preMergeSort : ∀ {TO} → List $ SortedList TO → List $ SortedList TO
preMergeSort [] = []
preMergeSort (x ∷ []) = x ∷ []
preMergeSort (x ∷ y ∷ l) = preMergeSort ((merge x y) ∷ preMergeSort l)

mergeSortAlt : ∀ {TO} → List $ TotalOrder.Carrier TO → SortedList TO
mergeSortAlt l with preMergeSort (mergePrep l)
... | [] = []
... | x ∷ r = x

-- to test, run: mSorta {ℕTO} SomeNats
mSorta : ∀ {TO} → List $ TotalOrder.Carrier TO → List $ TotalOrder.Carrier TO
mSorta {TO} = ForgetSorting {TO} ∘ mergeSortAlt



-- ============ Natural Number Total order for testing ==========
R≤ : _≡_ ⇒ _≤_
R≤ {zero} refl = z≤n
R≤ {suc i} refl = s≤s (R≤ {i} refl)

T≤ : Transitive _≤_
T≤ z≤n _ = z≤n
T≤ (s≤s x) (s≤s y) = s≤s (T≤ x y)

AS≡≤ : Antisymmetric _≡_ _≤_
AS≡≤ z≤n z≤n = refl
AS≡≤ {suc m} {suc n} (s≤s x) (s≤s y) = rsuc (AS≡≤ {m} {n} x y) where
 rsuc : ∀ {m n} → m ≡ n → suc m ≡ suc n
 rsuc refl = refl

To≤ : Total _≤_
To≤ zero zero = inj₁ z≤n
To≤ zero (suc _) = inj₁ z≤n
To≤ (suc _) zero = inj₂ z≤n
To≤ (suc x) (suc y) with To≤ x y
... | inj₁ x≤y = inj₁ (s≤s x≤y)
... | inj₂ y≤x = inj₂ (s≤s y≤x)

ℕTO : TotalOrder lzero lzero lzero
ℕTO = record {
 Carrier = ℕ ; _≈_ = _≡_ ; _≤_ = _≤_ ;
 isTotalOrder = record {
  isPartialOrder = record {
   isPreorder = record {
    isEquivalence = record { refl = refl ; sym = sym ; trans = trans } ;
    reflexive = R≤ ;
    trans = T≤ } ;
   antisym = AS≡≤ } ;
  total = To≤ } }

SomeNats : List ℕ
SomeNats = 8 ∷ 4 ∷ 5 ∷ 1 ∷ 3 ∷ 9 ∷ 2 ∷ 6 ∷ 7 ∷ []
