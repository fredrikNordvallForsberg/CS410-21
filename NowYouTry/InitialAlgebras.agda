module NowYouTry.InitialAlgebras where

open import Data.Bool
open import Data.Unit
open import Data.Empty
open import Data.Product

open import Relation.Binary.PropositionalEquality

open import Function

open import Common.Category

open import Lectures.DataData
open import Lectures.DescFreeMonad

---------------------------------------------------------------------------
-- ℕ is an initial algebra
---------------------------------------------------------------------------

Argsℕ = DESC.Args U El natCode
conℕ = DESC.con {d = natCode}
Argsℕ-map = Args-map U El natCode

Argsℕ-id : ∀ {A} → (x : Argsℕ A) → Argsℕ-map (λ x₁ → x₁) x ≡ x
Argsℕ-id = Args-id U El natCode

Argsℕ-compose : ∀ {X Y Z}{f : X -> Y}{g : Y -> Z} →
                (x : Argsℕ X) → Argsℕ-map (λ x₁ → g (f x₁)) x ≡ Argsℕ-map g (Argsℕ-map f x)
Argsℕ-compose = Args-compose U El natCode



foldℕ : {A : Set} -> (f : Argsℕ A -> A) ->
        ℕ' -> A
foldℕ f zero' = f (true , tt)
foldℕ f (suc' x) = f (false , foldℕ f x)

foldℕ-mediates : ∀ {A f} ->
                 foldℕ {A = A} f ∘′ conℕ ≡ f ∘′ Argsℕ-map (foldℕ f)
foldℕ-mediates {A} {f} = ext lemma where
  lemma : ∀ n → (foldℕ {A = A} f ∘′ conℕ) n ≡ (f ∘′ Argsℕ-map (foldℕ f)) n
  lemma (true , tt) = refl
  lemma (false , x) = refl

foldℕ-unique : ∀ {A f} -> (h : ℕ' -> A) ->
               h ∘′ conℕ ≡ f ∘′ Argsℕ-map h ->
               (n : ℕ') -> h n ≡ foldℕ f n
foldℕ-unique h p zero' = cong-app p (true , tt)
foldℕ-unique {f = f} h p (suc' n) = trans (cong-app p (false , n)) (cong (λ z → f (false , z)) (foldℕ-unique h p n))

module _ (U : Set)(El : U -> Set) where

  open DESC U El

  ---------------------------------------------------------------------------
  -- Data types are initial algebras
  ---------------------------------------------------------------------------

  mutual

    Args-fold : {c : Desc}(d : Desc) -> {A : Set} -> (f : Args c A -> A) ->
                Args d ⟦ c ⟧Desc -> Args d A
    Args-fold `⊤ f _ = tt
    Args-fold (`Σ a b) f (x , y) = (x , Args-fold (b x) f y)
    Args-fold (d `× e) f (x , y) = Args-fold d f x , Args-fold e f y
    Args-fold `X f x = fold _ f x

    fold : (d : Desc) -> {A : Set} -> (f : Args d A -> A) ->
           ⟦ d ⟧Desc -> A
    fold d f (con x) = f (Args-fold d f x)

  Args-fold-is-Args-map : {c : Desc}(d : Desc) -> {A : Set} -> (f : Args c A -> A) ->
                (x : Args d ⟦ c ⟧Desc) -> Args-fold d f x ≡ Args-map U El d (fold c f) x
  Args-fold-is-Args-map `⊤ f tt = refl
  Args-fold-is-Args-map (`Σ a b) f (x , y) = cong (x ,_) (Args-fold-is-Args-map (b x) f y)
  Args-fold-is-Args-map (d `× e) f (x , y) = cong₂ _,_ (Args-fold-is-Args-map d f x) (Args-fold-is-Args-map e f y)
  Args-fold-is-Args-map `X f x = refl

  fold-mediates : ∀ {A} d {f : Args d A -> A} ->
                   fold d f ∘′ con ≡ f ∘′ Args-map U El d (fold d f)
  fold-mediates d {f} = ext λ x → cong f (Args-fold-is-Args-map d f x )

  mutual

    Args-h-is-Args-fold : ∀ {c} d {A f} -> (h : ⟦ c ⟧Desc -> A) ->
                          h ∘′ con ≡ f ∘′ Args-map U El c h ->
                          (x : Args d ⟦ c ⟧Desc) → Args-map U El d h x ≡ Args-fold d f x
    Args-h-is-Args-fold `⊤ p h x = refl
    Args-h-is-Args-fold (`Σ a b) p h (x , y) = cong (x ,_) (Args-h-is-Args-fold (b x) p h y)
    Args-h-is-Args-fold (d `× e) p h (x , y) = cong₂ _,_ (Args-h-is-Args-fold d p h x) (Args-h-is-Args-fold e p h y)
    Args-h-is-Args-fold `X p h x = fold-unique _ p h x

    fold-unique : ∀ d {A f} -> (h : ⟦ d ⟧Desc -> A) ->
                  h ∘′ con ≡ f ∘′ Args-map U El d h ->
                  (x : ⟦ d ⟧Desc) -> h x ≡ fold d f x
    fold-unique d {f = f} h p (con x) = trans (cong-app p x) (cong f (Args-h-is-Args-fold d h p x))


---------------------------------------------------------------------------
-- Induction from initiality
---------------------------------------------------------------------------

induction : (P : ℕ' -> Set) -> P zero' -> (∀ n → P n -> P (suc' n)) -> ∀ n → P n
induction P pz ps n = subst P (fst-is-untouched n) (proj₂ (some-P n)) where

  con* : Argsℕ (Σ ℕ' P) -> Σ ℕ' P
  con* (true , _) = zero' , pz
  con* (false , (n , pn)) = (suc' n) , ps n pn

  some-P : ℕ' -> Σ ℕ' P
  some-P n = foldℕ {A = Σ ℕ' P} con* n

  fst-is-untouched : ∀ n → proj₁ (some-P n) ≡ n
  fst-is-untouched n = begin
    proj₁ (some-P n)
      ≡⟨ foldℕ-unique (proj₁ ∘′ foldℕ con*) (ext proj₁∘some-P-alg) n ⟩
    foldℕ conℕ n
      ≡⟨ sym (foldℕ-unique id (ext λ x → cong conℕ (sym (Argsℕ-id x))) n) ⟩
    n
      ∎
    where
      open ≡-Reasoning
      proj₁∘some-P-alg : ∀ x → proj₁ (foldℕ con* (conℕ x)) ≡ conℕ (Argsℕ-map (proj₁ ∘′ some-P) x)
      proj₁∘some-P-alg (true , snd) = refl
      proj₁∘some-P-alg (false , snd) = refl

---------------------------------------------------------------------------
-- Now you try
---------------------------------------------------------------------------

open ≡-Reasoning

-- For every initial algebra, con : F X -> X is an isomorphism

lambek : ℕ' -> Argsℕ ℕ'
lambek n = {!!}  -- using foldℕ and Argsℕ-map

lambek∘con=id : ∀ n → conℕ (lambek n) ≡ n
lambek∘con=id n = begin
  conℕ (lambek n)
    ≡⟨ {!foldℕ-unique {!!} {!!} n!} ⟩
  foldℕ conℕ n
    ≡⟨ sym (foldℕ-unique id (ext λ x → cong conℕ (sym (Argsℕ-id x))) n) ⟩
  n
  ∎

con∘lambek=id : ∀ x → lambek (conℕ x) ≡ x
con∘lambek=id x = begin
  lambek (conℕ x)
    ≡⟨ {!!} ⟩
  Argsℕ-map conℕ (Argsℕ-map lambek x)
    ≡⟨ {!!} ⟩
  Argsℕ-map (conℕ ∘′ lambek) x
    ≡⟨ cong (λ z → Argsℕ-map z x) {!!} ⟩
  Argsℕ-map id x
    ≡⟨ Argsℕ-id x ⟩
  x
  ∎
