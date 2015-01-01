open import Data.Nat
open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Empty
open import Data.Bool
open import Relation.Nullary

-- A straightforward definition of surjection
record _↠_ (A B : Set) : Set where
 constructor sur
 field
  to : A → B
  rightInv : Σ[ g ∈ (B → A) ] (∀ x → to (g x) ≡ x)

-- The type of proofs that a function has no fixed point
record NoFixpoint {A : Set} (f : A → A) : Set where
 constructor nf
 field
  noFix : ∀ a → f a ≢ a

--======== Lemmas for working with surjections, and in preparation for Cantor's theorem. Probably could be done better =======
--A surjection contains a function
canLem1 : {A B : Set} → (A ↠ B) → A → B
canLem1 (sur to _) = to

--Diagnalization
canLem2 : {T S Y : Set} → (T → S → Y) → T × S → Y
canLem2 f (p₁ , p₂) = f p₁ p₂

--if f is a (higher-order) surjection and f' is the right inverse of f, then f (f' x) t = x t
lem : {A B : Set} → (to : A → A → B) → (from : (A → B) → A) → (∀ a → to (from a) ≡ a) → ∀ g t → to (from g) t ≡ g t
lem to from pr g t rewrite pr g = refl

{-
 This is the first real step in the proof. For any surjection s : T ↠ (T → Y), and any function g : T → Y,
one can use s to represent g, using the diagnalization from earlier.
-}
canLem : {T Y : Set} → (sr : T ↠ (T → Y)) → (g : T → Y) → Σ[ x ∈ T ] (∀ t → canLem2 (canLem1 sr) (x , t) ≡ g t)
canLem {T} {Y} (sur to (from , ff'x≡x)) g rewrite ff'x≡x g = from g , lem to from ff'x≡x g

{-
 A generalization of cantor's proof over arbitrary types. We assume that α is a function with no fixed point,
and then assume a surjection. From there, we define f as the diagnanalization of our surjection. We then define our
counter-example function g in terms of α and f. We then extract the representation of g using canLem. We define t₀
as the element which happens to produce g (there has to be at least one). We then prove that f (t₀ , t₀) ≡ g t₀
by observing that the representation of g is the same diagnalization that we defined f to be. From there, the
proof goes through straightforwardly.
-}
SetFx : {T Y : Set} → (α : Y → Y) → NoFixpoint α → ¬ (T ↠ (T → Y))
SetFx {T} {Y} α (nf noFix) sr = noFix (f (t₀ , t₀)) e3 where
 f : T × T → Y
 f = canLem2 (canLem1 sr)

 g : T → Y
 g x = α (f (x , x))

 t₀ : T
 t₀ = proj₁ $ canLem sr g

 e2 : f (t₀ , t₀) ≡ g t₀
 e2 = (proj₂ $ canLem sr g) t₀

 e3 : α (f (t₀ , t₀)) ≡ f (t₀ , t₀)
 e3 rewrite sym e2 = refl

--Cantor's Theorem. Here, the not function is used for its lack of fixed point.
Cantor : ¬ (ℕ ↠ (ℕ → Bool))
Cantor = SetFx not (nf helper) where
 helper : (a : Bool) → not a ≢ a
 helper true ()
 helper false ()
