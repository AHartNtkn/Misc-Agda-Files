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
data NoFixpoint {A : Set} (f : A → A) : Set where
 nf : (∀ a → f a ≢ a) → NoFixpoint f

data Fixpoint {A : Set} (f : A → A) : Set where
 fp : Σ[ a ∈ A ] f a ≡ a → Fixpoint f

--======== Lemmas for working with surjections, and in preparation for Cantor's theorem. Probably could be done better =======
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
canLem : {T Y : Set} → (sr : T ↠ (T → Y)) → (g : T → Y) → Σ[ x ∈ T ] (∀ t → canLem2 (_↠_.to sr) (x , t) ≡ g t)
canLem {T} {Y} (sur to (from , ff'x≡x)) g = from g , lem to from ff'x≡x g

{-
 A generalization of cantor's proof over arbitrary types. We assume that α is a function with no fixed point,
and then assume a surjection. From there, we define f as the diagnanalization of our surjection. We then define our
counter-example function g in terms of α and f. We then extract the representation of g using canLem. We define t₀
as the element which happens to produce g (there has to be at least one). We then prove that f (t₀ , t₀) ≡ g t₀
by observing that the representation of g is the same diagnalization that we defined f to be. From there, the
proof goes through straightforwardly.
-}
SetFp : {T Y : Set} → (T ↠ (T → Y)) → (α : Y → Y) → Fixpoint α
SetFp {T} {Y} sr α = fp (f (t₀ , t₀) , e3) where
 f : T × T → Y
 f = canLem2 (_↠_.to sr)

 g : T → Y
 g x = α (f (x , x))

 t₀ : T
 t₀ = proj₁ $ canLem sr g

 e2 : f (t₀ , t₀) ≡ g t₀
 e2 = (proj₂ $ canLem sr g) t₀

 e3 : α (f (t₀ , t₀)) ≡ f (t₀ , t₀)
 e3 rewrite sym e2 = refl

SetFx : {T Y : Set} → (α : Y → Y) → NoFixpoint α → ¬ (T ↠ (T → Y))
SetFx α (nf noFix) sr with SetFp sr α
... | fp (p₁ , p₂) = noFix p₁ p₂

--Cantor's Theorem. Here, the not function is used for its lack of fixed point.
Cantor : ¬ (ℕ ↠ (ℕ → Bool))
Cantor = SetFx not (nf hlpr) where
 hlpr : (a : Bool) → not a ≢ a
 hlpr true  ()
 hlpr false ()
