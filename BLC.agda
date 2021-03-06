module BLC where

open import Data.Nat
open import Relation.Nullary.Core
open import Function
open import Relation.Binary
open import Data.Empty
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Digit
open import Data.Fin hiding (_+_)
open import Data.List
open import Data.String renaming (_++_ to _s++_) hiding (_≟_)

Nest : ∀ {l} {A : Set l} → (A → A) → A → ℕ → A
Nest f a 0 = a
Nest f a (suc n) = Nest f (f a) n

-- NOTE: Almost everything here is poorly tested. And one should always be weary when overusing NON_TERMINATING

-- ================= Untyped Lambda Calculus ===========
data LambdaTerm : Set where
 λₜ : ℕ → LambdaTerm → LambdaTerm
 vₜ : ℕ → LambdaTerm -- Variables are uniquely identified by a number
 _·_ : LambdaTerm → LambdaTerm → LambdaTerm

-- A single step in lambda calculus evaluation
λSimp : LambdaTerm → LambdaTerm
λSimp (λₜ x x₁) = λₜ x (λSimp x₁)
λSimp (vₜ x) = vₜ x
λSimp (λₜ x (λₜ y e₂) · e₁) with x ≟ y
... | yes p = λₜ x (λSimp e₂)
... | no ¬p = λₜ y (λSimp ((λₜ x e₂) · e₁))
λSimp (λₜ x (vₜ y) · e) with x ≟ y
... | yes p = λSimp e
... | no ¬p = vₜ y
λSimp (λₜ x (e₂ · e₃) · e₁) =
 (λSimp ((λₜ x e₂) · e₁) · λSimp ((λₜ x e₃) · e₁))
λSimp (vₜ x · x₁) = (vₜ x · λSimp x₁)
λSimp ((x · x₁) · x₂) = (λSimp (x · x₁) · λSimp x₂)

{- Non-terminating version of λSimp. Makes λEV faster?
{-# NON_TERMINATING #-}
λSimp : LambdaTerm → LambdaTerm
λSimp (λₜ x x₁) = λₜ x (λSimp x₁)
λSimp (vₜ x) = vₜ x
λSimp (λₜ x (λₜ y e₂) · e₁) with x ≟ y
... | yes p = λSimp $ λₜ x (λSimp e₂)
... | no ¬p = λSimp $ λₜ y (λSimp ((λₜ x e₂) · e₁))
λSimp (λₜ x (vₜ y) · e) with x ≟ y
... | yes p = λSimp e
... | no ¬p = vₜ y
λSimp (λₜ x (e₂ · e₃) · e₁) =
 (λSimp (λSimp ((λₜ x e₂) · e₁)) · λSimp ((λₜ x e₃) · e₁))
λSimp (vₜ x · x₁) = (vₜ x · λSimp x₁)
λSimp ((x · x₁) · x₂) = (λSimp (x · x₁) · λSimp x₂)
-}

-- Example lambda term
λid : LambdaTerm
λid = λₜ 1 $ vₜ 1


-- ============= Martin Lof Equality is decidable over lambda terms ========
λlem1 : ∀ {x y}{a b : LambdaTerm} → _≡_ {A = LambdaTerm} (λₜ x a) (λₜ y b) → a ≡ b × x ≡ y
λlem1 refl = refl , refl

λlem2 : {a b : ℕ} → _≡_ {A = LambdaTerm} (vₜ a) (vₜ b) → a ≡ b
λlem2 refl = refl

λlem3 : {a b x y : LambdaTerm} → _≡_ {A = LambdaTerm} (a · x) (b · y) → a ≡ b × x ≡ y
λlem3 refl = refl , refl

_λ≟_ : Decidable {A = LambdaTerm} _≡_
λₜ x t λ≟ λₜ y t₁ with x ≟ y | t λ≟ t₁
λₜ x t λ≟ λₜ .x .t | yes refl | yes refl = yes refl
λₜ x t λ≟ λₜ .x t₁ | yes refl | no ¬p = no $ ¬p ∘ proj₁ ∘ λlem1
... | no ¬p | r = no $ ¬p ∘ proj₂ ∘ λlem1
λₜ x t λ≟ vₜ x₁ = no (λ ())
λₜ x t λ≟ t₁ · t₂ = no (λ ())
vₜ x λ≟ λₜ x₁ t₁ = no (λ ())
vₜ x λ≟ vₜ y with x ≟ y 
vₜ x λ≟ vₜ .x | yes refl = yes refl
... | no ¬p = no $ ¬p ∘ λlem2
vₜ x λ≟ t₁ · t₂ = no (λ ())
t · t₁ λ≟ λₜ x t₂ = no (λ ())
t · t₁ λ≟ vₜ x = no (λ ())
t · t₁ λ≟ t₂ · t₃ with t λ≟ t₂ | t₁ λ≟ t₃
t · t₁ λ≟ .t · .t₁ | yes refl | yes refl = yes refl
... | yes _ | no ¬p = no $ ¬p ∘ proj₂ ∘ λlem3
... | no ¬p | yes _ = no $ ¬p ∘ proj₁ ∘ λlem3
... | no ¬p | no  _ = no $ ¬p ∘ proj₁ ∘ λlem3

-- Keep evaluating as long as λEV is making changes
{-# NON_TERMINATING #-}
λEV : LambdaTerm → LambdaTerm
λEV l with λSimp l λ≟ l
... | yes p = l
... | no ¬p = λEV $ λSimp l

-- ============== Untyped SK Combinator Calculus ==========
data SK : Set where
 k : SK
 s : SK
 _·_ : SK → SK → SK

SKSimp : SK → SK
SKSimp k = k
SKSimp s = s
SKSimp (k · x) = k · SKSimp x
SKSimp (s · x) = s · SKSimp x
SKSimp ((k · x) · y) = SKSimp x
SKSimp ((s · x) · y) = (s · SKSimp x) · SKSimp y
SKSimp (((k · x) · y) · z) = SKSimp x · SKSimp z
SKSimp (((s · x) · y) · z) = SKSimp (x · z) · SKSimp (y · z)
SKSimp ((((x · y) · z) · w) · v) = SKSimp (((x · y) · z) · w) · SKSimp v

SKid : SK
SKid = (s · k) · k

SKTest : SK
SKTest = (((((((s · k) · k) · k) · k) · k) · s) · k) · k

-- ============= Martin Lof Equality is decidable over SK terms ========
SKlem : {a b x y : SK} → _≡_ {A = SK} (a · x) (b · y) → a ≡ b × x ≡ y
SKlem refl = refl , refl

_SK≟_ : Decidable {A = SK} _≡_
k SK≟ k = yes refl
k SK≟ s = no (λ ())
k SK≟ b · b₁ = no (λ ())
s SK≟ k = no (λ ())
s SK≟ s = yes refl
s SK≟ b · b₁ = no (λ ())
a · a₁ SK≟ k = no (λ ())
a · a₁ SK≟ s = no (λ ())
a · a₁ SK≟ b · b₁ with a SK≟ b | a₁ SK≟ b₁
a · a₁ SK≟ .a · .a₁ | yes refl | yes refl = yes refl
... | yes _    | no ¬p    = no $ ¬p ∘ proj₂ ∘ SKlem
... | no ¬p    | yes _    = no $ ¬p ∘ proj₁ ∘ SKlem
... | no ¬p    | no ¬p₁   = no $ ¬p ∘ proj₁ ∘ SKlem

-- Keep evaluating as long as SKSimp is making changes
{-# NON_TERMINATING #-}
SKEV : SK → SK
SKEV l with SKSimp l SK≟ l
... | yes p = l
... | no ¬p = SKEV $ SKSimp l

-- =============== Translate a Lambda program into an SK program ========
{-# NON_TERMINATING #-}
λ→SK : LambdaTerm → SK
λ→SK (λₜ n (λₜ x y)) = k · λ→SK (λₜ x y)
λ→SK (λₜ n (vₜ m)) with n ≟ m
... | yes p = (s · k) · k
... | no ¬p = k · ((s · k) · k)
λ→SK (λₜ n (x · y)) = (s · (λ→SK $ λₜ n x)) · (λ→SK $ λₜ n y)
λ→SK (vₜ x) = (s · k) · k
λ→SK (x · y) = λ→SK x · λ→SK y

-- =============== Translate an SK program into a Lambda program ========
SK→λ' : ℕ → SK → LambdaTerm
SK→λ' n k =
 λₜ (1 + n) $ λₜ (2 + n) $ vₜ (1 + n) 
SK→λ' n s =
 λₜ (1 + n) $ λₜ (2 + n) $ λₜ (3 + n) $ 
  (vₜ (1 + n) · vₜ (3 + n)) · (vₜ (2 + n) · vₜ (3 + n))
SK→λ' n (x · y) = SK→λ' (suc n) x · SK→λ' (suc n) y

SK→λ : SK → LambdaTerm
SK→λ x = SK→λ' 0 x

-- ============== Define an implementation of Jot, with each program represented by a Binary
data Binary : Set where
 eb : Binary
 0S : Binary → Binary
 1S : Binary → Binary

-- Jot Compiler
Bin→λ : ℕ → Binary → LambdaTerm
Bin→λ n eb = λₜ (1 + n) $ vₜ (1 + n)
Bin→λ n (0S b) = λSimp (((Bin→λ (1 + n) b) · (SK→λ' (1 + n) s)) · (SK→λ' (1 + n) k)) 
Bin→λ n (1S b) = λSimp (((SK→λ' (1 + n) s) · (SK→λ' (1 + n) k)) · (Bin→λ (1 + n) b))


-- ============ Binary manipulations ===========
_B++_ : Binary → Binary → Binary
_B++_ eb b2 = b2
_B++_ (0S b1) b2 = 0S $ (b1 B++ b2)
_B++_ (1S b1) b2 = 1S $ (b1 B++ b2)

ReverseBin : Binary → Binary
ReverseBin eb = eb
ReverseBin (0S b) = (ReverseBin b) B++ (0S eb)
ReverseBin (1S b) = (ReverseBin b) B++ (1S eb)

SK→Bin : SK → Binary
SK→Bin k = 0S $ 0S $ 1S $ 1S $ 1S $ eb
SK→Bin s = 0S $ 0S $ 0S $ 1S $ 1S $ 1S $ 1S $ 1S $ eb
SK→Bin (n · m) = ((SK→Bin m) B++ (SK→Bin n)) B++ (1S eb)

-- Translate an SK program into a Jot program
SK→Jot : SK → Binary
SK→Jot = ReverseBin ∘ SK→Bin

λ→Bin : LambdaTerm → Binary
λ→Bin = SK→Bin ∘ λ→SK

-- Translate a lambda program into a Jot program
λ→Jot : LambdaTerm → Binary
λ→Jot = SK→Jot ∘ λ→SK

-- ============ Translate binary strings into numbers, and vice versa =========

Bin→Base : Binary → List $ Fin 2
Bin→Base eb = []
Bin→Base (0S b) = zero ∷ Bin→Base b
Bin→Base (1S b) = (suc zero) ∷ Bin→Base b

Base→Bin : List $ Fin 2 → Binary
Base→Bin [] = eb
Base→Bin (zero ∷ l) = 0S (Base→Bin l)
Base→Bin (suc x ∷ l) = 1S (Base→Bin l)

Bin→ℕ : Binary → ℕ
Bin→ℕ = fromDigits ∘ Bin→Base ∘ 1S

ℕ→Bin : ℕ → Binary
ℕ→Bin n = Base→Bin $ drop 1 $ proj₁ $ toDigits 2 n

{- A universal function based on Jot
λ→ℕ : LambdaTerm → ℕ
λ→ℕ = Bin→ℕ ∘ λ→Bin
U : ℕ → LambdaTerm
U = Bin→λ 0 ∘ ℕ→Bin
-}

one : ℕ → LambdaTerm
one f = λₜ f (λₜ (1 + f) (vₜ f · vₜ (1 + f)))

{-
one' : LambdaTerm
one' = U 4395017348949468060
-}

-- ========== deBrujin definition ==========
infixl 80 _·_
data deBrujin : Set where
  λₜ : deBrujin → deBrujin
  vₜ : ℕ → deBrujin
  _·_ : deBrujin → deBrujin → deBrujin

-- Some example programs
did : deBrujin
did = λₜ (vₜ 0)

ex1 : deBrujin
ex1 = λₜ (λₜ (vₜ 0)) · (vₜ 0)

ex2 : ℕ → deBrujin
ex2 n = λₜ (λₜ (λₜ (vₜ n)) · (vₜ 0))

ex3 : ℕ → deBrujin
ex3 n = λₜ (λₜ (λₜ (λₜ (vₜ n)) · (vₜ 1)))

ex4 : deBrujin
ex4 = λₜ (λₜ (λₜ (vₜ 1)) · (λₜ (vₜ 0 · vₜ 0)))


-- ============= deBrujin implementation via translation to ordinary lambda terms ==========
-- These are modified from functions found here: http://homepages.cwi.nl/~tromp/cl/HOAS.lhs

fromDB : deBrujin → LambdaTerm
fromDB = cnvt 0 [] where
 cnvt : ℕ → List LambdaTerm → deBrujin → LambdaTerm
 cnvt n e (λₜ t) = λₜ n (cnvt (suc n) (vₜ n ∷ e) t)
 cnvt n [] (vₜ x) = vₜ x
 cnvt n (e₁ ∷ e) (vₜ 0) = e₁
 cnvt n (_ ∷ e) (vₜ (suc x)) = cnvt n e (vₜ x)
 cnvt n e (t · t₁) = cnvt n e t · cnvt n e t₁


toDB : LambdaTerm → deBrujin
toDB = cnvt 0 where
 cnvt : ℕ → LambdaTerm → deBrujin
 cnvt n (λₜ x t) = λₜ (cnvt (suc x) t)
 cnvt n (vₜ x) = vₜ (n ∸ suc x)
 cnvt n (t · t₁) = cnvt n t · cnvt n t₁

tEval : deBrujin → deBrujin
tEval = toDB ∘ λEV ∘ fromDB


-- ============ Binary Lambda Calculus Compiler =========

-- Generate BLC program from deBrujin terms
λ→BLC : deBrujin → Binary
λ→BLC (λₜ t) = 0S $ 0S $ λ→BLC t
λ→BLC (vₜ x) = gennum (x + 1) B++ (0S $ eb) where
 gennum : ℕ → Binary
 gennum zero = eb
 gennum (suc n) = 1S $ gennum n
λ→BLC (t · t₁) = 0S $ 1S $ (λ→BLC t B++ λ→BLC t₁)

-- Dummy type for parsing from the left
data pseudodB : Set where
 λₜ : pseudodB
 ·· : pseudodB
 vₜ : ℕ → pseudodB

-- extract an index variable number from a BLC string
ne : Binary → ℕ × Binary
ne eb = zero , eb
ne (0S b) = zero , b
ne (1S b) = suc (proj₁ $ ne b) , (proj₂ $ ne b)

-- Parse the operator structure
{-# TERMINATING #-}
PreParse : Binary → List pseudodB
PreParse eb = []
PreParse (0S eb) = []
PreParse (0S (0S b)) = λₜ ∷ PreParse b
PreParse (0S (1S b)) = ·· ∷ PreParse b
PreParse (1S b) = (vₜ (proj₁ $ ne b)) ∷ (PreParse $ proj₂ $ ne b)

-- Parse the tree structure
StkParse : List deBrujin → List pseudodB → deBrujin
StkParse [] [] = did
StkParse [] (λₜ ∷ l2) = did
StkParse [] (·· ∷ l2) = did
StkParse [] (vₜ n ∷ l2) = StkParse (vₜ n ∷ []) l2
StkParse (x ∷ l1) [] = x
StkParse (x ∷ l1) (λₜ ∷ l2) = StkParse (λₜ x ∷ l1) l2
StkParse (x ∷ []) (·· ∷ l2) = did
StkParse (x ∷ y ∷ l1) (·· ∷ l2) = StkParse (x · y ∷ l1) l2
StkParse (x ∷ l1) (vₜ n ∷ l2) = StkParse (vₜ n ∷ x ∷ l1) l2

-- full parse
BLC→λ : Binary → deBrujin
BLC→λ = StkParse [] ∘ reverse ∘ PreParse

-- Actual compiler
BLCCompiler : Binary → Binary
BLCCompiler = λ→BLC ∘ tEval ∘ BLC→λ

-- ========== Universal function based on BLC =============
ℕ→λ : ℕ → deBrujin
ℕ→λ = BLC→λ ∘ ℕ→Bin

λ→ℕ : deBrujin → ℕ
λ→ℕ = Bin→ℕ ∘ λ→BLC

U : ℕ → deBrujin
U = tEval ∘ ℕ→λ



-- Church numeral generator for testing
ChurchNumeral : ℕ → ℕ → ℕ → LambdaTerm
ChurchNumeral n f x = λₜ f (λₜ x (Nest (_·_ (vₜ f)) (vₜ x) n))

CN : ℕ → deBrujin
CN n = λₜ (λₜ (Nest (_·_ (vₜ 1)) (vₜ 0) n))

two = CN 2

add : deBrujin
add = λₜ (λₜ (λₜ (λₜ (vₜ 3 · vₜ 1 · (vₜ 2 · vₜ 1 · vₜ 0)))))

twoplustwo : deBrujin
twoplustwo = add · two · two

-- to test, run: NEV (add · (CN 3) · (CN 5))


-- ============= Stuff for IO ===========

pr : Binary → String
pr eb     = ""
pr (0S b) = "0" s++ pr b
pr (1S b) = "1" s++ pr b

{-# NON_TERMINATING #-}
String→Binary : String → Binary
String→Binary str with toList str
... | []      = eb
... | '0' ∷ r = 0S $ String→Binary $ fromList r
... | '1' ∷ r = 1S $ String→Binary $ fromList r
... | x   ∷ r = eb

BLCInterpreter : String → String
BLCInterpreter = pr ∘ BLCCompiler ∘ String→Binary

-- pr $ λ→BLC (add · (CN 3) · (CN 5)) returns 
-- "01010000000001011111011001011110110100000011100111001110100000011100111001110011100111010"

-- pr $ λ→BLC (CN 8) returns
-- "0000011100111001110011100111001110011100111010"

-- BLCInterpreter "01010000000001011111011001011110110100000011100111001110100000011100111001110011100111010" returns
-- "0000011100111001110011100111001110011100111010"

-- This is correct





















-- ========= a messy deBrujin lambda calculus implementation ===========
-- Seems to work, but I'm not sure. A typed version would be able to confirm.

RaiseUp : ℕ → deBrujin → deBrujin
RaiseUp n (λₜ b) = λₜ (RaiseUp (suc n) b)
RaiseUp n (vₜ m) with m ≤? n
... | yes p = vₜ m
... | no ¬p = vₜ (m ∸ 1)
RaiseUp n (b · d) = RaiseUp n b · RaiseUp n d

Replace : ℕ → deBrujin → deBrujin → deBrujin
Replace n x (λₜ y) = λₜ (Replace (suc n) (RaiseUp (suc n) x) y)
Replace n x (vₜ m) with n ≟ m
... | yes p = x
... | no ¬p = vₜ m
Replace n x (y · z) = Replace n x y · Replace n x z

-- Single evaluation step
Eval : deBrujin → deBrujin
Eval (λₜ e) = λₜ (Eval e)
Eval (vₜ x) = vₜ x
Eval (λₜ e1 · e2) = (Replace 0 e2 e1)
Eval (vₜ x · e) = vₜ x · Eval e
Eval ((e1 · e2) · e3) = Eval (e1 · e2) · Eval e3


-- ============= Proof that Martin-Lof equality over deBrujin lambda terms is decidable ============
lem1 : {a b : deBrujin} → _≡_ {A = deBrujin} (λₜ a) (λₜ b) → a ≡ b
lem1 refl = refl

lem2 : {a b : ℕ} → _≡_ {A = deBrujin} (vₜ a) (vₜ b) → a ≡ b
lem2 refl = refl

lem3 : {a b x y : deBrujin} → _≡_ {A = deBrujin} (a · x) (b · y) → a ≡ b × x ≡ y
lem3 refl = refl , refl

_dB≟_ : Decidable {A = deBrujin} _≡_
λₜ a dB≟ λₜ b with a dB≟ b
λₜ a dB≟ λₜ .a | yes refl = yes refl
... | no ¬p = no $ ¬p ∘ lem1
λₜ _ dB≟ vₜ _ = no λ ()
λₜ _ dB≟ (_ · _) = no λ ()
vₜ _ dB≟ λₜ _ = no λ ()
vₜ x dB≟ vₜ y with x ≟ y
vₜ x dB≟ vₜ .x | yes refl = yes refl
... | no ¬p = no $ ¬p ∘ lem2
vₜ _ dB≟ (_ · _) = no λ ()
(_ · _) dB≟ λₜ _ = no λ ()
(_ · _) dB≟ vₜ _ = no λ ()
(a · a₁) dB≟ (b · b₁) with a dB≟ b | a₁ dB≟ b₁
(a · a₁) dB≟ (.a · .a₁) | yes refl | yes refl = yes refl
... | yes _ | no ¬p = no $ ¬p ∘ proj₂ ∘ lem3
... | no ¬p | yes _ = no $ ¬p ∘ proj₁ ∘ lem3
... | no ¬p | no  _ = no $ ¬p ∘ proj₁ ∘ lem3

-- Keep evaluating as long as Eval changes the expression
{-# NON_TERMINATING #-}
NEV : deBrujin → deBrujin
NEV d with d dB≟ Eval d
NEV d | yes p = d
NEV d | no ¬p = NEV $ Eval d
