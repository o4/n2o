{-# OPTIONS --cubical --safe #-}
module Infinity.Path where

open import Infinity.Core public
open import Infinity.Proto
open import Infinity.Sigma

module _ {ℓ} {A : Set ℓ} where

  compPath : {x y z : A} → Path A x y → Path A y z → Path A x z
  compPath {x} {y} p q = λ i → primComp (λ j → A) _ (λ j → λ { (i = i1) → q j ; (i = i0) → x }) (p i)

  trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans {x = x} p q i = hcomp (λ j → \ { (i = i0) → x ; (i = i1) → q j }) (p i)

  refl : {x : A} → x ≡ x
  refl {x} = λ _ → x

  sym : {x y : A} → x ≡ y → y ≡ x
  sym p = λ i → p (~ i)

  cong : ∀ {ℓ'} {B : A → Set ℓ'} {x y : A} (f : (a : A) → B a) (p : x ≡ y) → PathP (λ i → B (p i)) (f x) (f y)
  cong f p = λ i → f (p i)

  coe : ∀ {ℓ : Level} {A B : Set ℓ} → A ≡ B → A → B
  coe p a = primComp (λ i → p i) i0 (λ _ → empty) a

module _ {ℓ ℓ'} {A : Set ℓ} {x : A} (P : ∀ y → x ≡ y → Set ℓ') (d : P x refl) where

  J : {y : A} → (p : x ≡ y) → P y p
  J p = transp (λ i → P (p i) (λ j → p (i ∧ j))) i0 d

  JRefl : J refl ≡ d
  JRefl i = transp (λ _ → P x refl) i d

module _ {ℓ ℓ'} {A : Set ℓ} (B : A → Set ℓ') where

  subst : {a b : A} (p : a ≡ b) → B a → B b
  subst p pa = transp (λ i → B (p i)) i0 pa

  substRefl : {a : A} (pa : B a) → subst refl pa ≡ pa
  substRefl {a} pa i = transp (λ _ → B a) i pa

  funExt : {f g : (x : A) → B x} → ((x : A) → f x ≡ g x) → f ≡ g
  funExt p i x = p x i

  transpRefl : ∀ {ℓ} (A : Set ℓ) (u0 : A) → PathP (λ _ → A) (transp (λ _ → A) i0 u0) u0
  transpRefl A u0 i = transp (λ _ → A) i u0

module _ {ℓ} {A : Set ℓ} where

  singl : (a : A) → Set ℓ
  singl a = Σ A (λ x → a ≡ x)

  contrSingl : {a b : A} (p : a ≡ b) → Path (singl a) (a , refl) (b , p)
  contrSingl p i = (p i , λ j → p (i ∧ j))

module _ {ℓ} {A : I → Set ℓ} {x : A i0} {y : A i1} where

  toPathP : transp A i0 x ≡ y → PathP A x y
  toPathP p i = hcomp (λ j → λ { (i = i0) → x ; (i = i1) → p j }) (transp (λ j → A (i ∧ j)) (~ i) x)

  fromPathP : PathP A x y → transp A i0 x ≡ y
  fromPathP p i = transp (λ j → A (i ∨ j)) i (p i)

module _ {ℓ} where

  isContr : Set ℓ → Set ℓ
  isContr A = Σ A (λ x → ∀ y → x ≡ y)

  isProp : Set ℓ → Set ℓ
  isProp A = (x y : A) → x ≡ y

  isSet : Set ℓ → Set ℓ
  isSet A = (x y : A) → isProp (x ≡ y)

nonDepPath : ∀ {ℓ} {A : Set ℓ} → (t u : A) → (t ≡ u) ≡ (PathP (λ i → A) t u)
nonDepPath _ _ = refl

isOfHLevel : ∀ {ℓ} → ℕ → Set ℓ → Set ℓ
isOfHLevel zero A = isContr A
isOfHLevel (succ n) A = (x y : A) → isOfHLevel n (x ≡ y)

HLevel : ∀ {ℓ} → ℕ → Set _
HLevel {ℓ} n = Σ[ A ∈ Set ℓ ] (isOfHLevel n A)

isContr→isProp : ∀ {A : Set ℓ} → isContr A → isProp A
isContr→isProp (x , p) a b i = hcomp (λ j → λ { (i = i0) → p a j ; (i = i1) → p b j }) x

inhProp→isContr : ∀ {A : Set ℓ} → A → isProp A → isContr A
inhProp→isContr x h = x , h x

isProp→isSet : ∀ {A : Set ℓ} → isProp A → isSet A
isProp→isSet h a b p q j i = hcomp (λ k → λ { (i = i0) → h a a k ; (i = i1) → h a b k
                                            ; (j = i0) → h a (p i) k ; (j = i1) → h a (q i) k }) a

isPropIsOfHLevel1 : ∀ {A : Set ℓ} → isProp A → isOfHLevel 1 A
isPropIsOfHLevel1 h x y = inhProp→isContr (h x y) (isProp→isSet h x y)

isPropIsProp : ∀ {A : Set ℓ} → isProp (isProp A)
isPropIsProp f g i a b = isProp→isSet f a b (f a b) (g a b) i

isPropIsSet : ∀ {A : Set ℓ} → isProp (isSet A)
isPropIsSet f g i a b = isPropIsProp (f a b) (g a b) i

isPropIsContr : ∀ {A : Set ℓ} → isProp (isContr A)
isPropIsContr z0 z1 j = ( z0 .π⃑ (z1 .π⃐) j , λ x i → hcomp (λ k → λ { (i = i0) → z0 .π⃑ (z1 .π⃐) j
                                                                   ; (i = i1) → z0 .π⃑ x (j ∨ k)
                                                                   ; (j = i0) → z0 .π⃑ x (i ∧ k)
                                                                   ; (j = i1) → z1 .π⃑ x i }) (z0 .π⃑ (z1 .π⃑ x i) j))
