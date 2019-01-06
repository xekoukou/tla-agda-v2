module TLA.RefineProp where


open import Level renaming (zero to lzero ; suc to lsuc ; Lift to ℓ↑)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List hiding (all)
open import Data.Product
open import Data.Bool
open import Data.Fin 
open import Data.Unit
open import Data.Fin.Properties
open import Data.Fin.Permutation
open import Function hiding (_⟨_⟩_ ; _$_)
open import Function.Inverse using (_↔_ ; Inverse)
open import Function.Equality using (Π)
open import TLA.Def
open import TLA.DefProp
open import TLA.Refine
open import TLA.Utils


open import LTL.Core renaming ([_] to [_]ₜ)
open import LTL.Stateless

-- Should we remove the bijection requirement?

record SpecEquality {α} {varsB varsA : LSet {α}} {varsA : LSet {α}}
                    (tcndB : Tcnd varsB) (tcndA : Tcnd varsA) : Set (lsuc α) where
  open Π
  field
    bijection : System varsB ↔ System varsA
    BtoA : GRef (Inverse.to bijection ⟨$⟩_) tcndB tcndA
    AtoB : GRef (Inverse.from bijection ⟨$⟩_) tcndA tcndB


record SpecEqualityᵣ {α} {varsB : LSet {α}} {varsA : LSet {α}}
               (specB : Spec varsB) (specA : Spec varsA) : Set (lsuc α) where
  open Π
  field
    bijection : System varsB ↔ System varsA
    BtoA : Ref (Inverse.to bijection ⟨$⟩_) specB specA
    AtoB : Ref (Inverse.from bijection ⟨$⟩_) specA specB



record SpecEqualityIᵣ {α} {varsB : LSet {α}} {varsA : LSet {α}}
               (speciB : SpecI varsB) (speciA : SpecI varsA) : Set (lsuc α) where
  open Π
  open SpecI
  field
    bijection : System varsB ↔ System varsA
    BtoA : RefI (Inverse.to bijection ⟨$⟩_) speciB speciA
    AtoB : RefI (Inverse.from bijection ⟨$⟩_) speciA speciB





ww : ∀{α} → {A : Set α} → (l : List A) → Permutation′ (length l) → List A
ww l per = tabulate (lookup l ∘ (per ⟨$⟩ˡ_))




-- bob : ∀{α} → {varsB : LSet {α}} → {varsA : LSet {α}}
--       → {specB : Spec varsB} → {specA : Spec varsA} → SpecEqualityᵣ specB specA → SpecEquality specB {!!} specA ?
-- bijection (bob speq) = bijection speq
-- BtoA (bob speq) pe beh rst = pb , {!!} where
--   eqq = eq (BtoA speq)
--   prst = subst (λ x → Σ ((PE x toUS)ʷ) (λ y → [ (x $ₛₚₜ y) beh ]ₜ) ) eqq (pe , rst)
--   pb = (⟨ exPar (rspec (BtoA speq)) ⟩ $ (proj₁ prst) $ beh)
--   rth = trefTh (rspec (BtoA speq)) beh (proj₁ prst) {!!}
-- AtoB (bob speq) = {!pe!}




-- ex-refm : ∀{α} → {varsB varsA varsC : LSet {α}} → (refm : System varsB → System varsA)
--           → (System (varsB ++ varsC) → System (varsA ++ varsC))
-- ex-refm refm sys = let (a , b) = splitₚ sys
--                    in refm a ++ₚ b

-- ex-gcnd : ∀{α} → {varsB varsC : LSet {α}}
--      → (gcond : GCond varsB)
--      → GCond (varsB ++ varsC)
-- ex-gcnd gcond sys = let (a , b) = splitₚ sys
--                     in gcond a

-- ee : ∀{α} → {varsB varsA varsC : LSet {α}}
--      → {refm : System varsB → System varsA}
--      → {gcond : GCond varsB} → {actA : Action varsA}
--      → RefAction refm gcond actA → RefAction (ex-refm {varsC = varsC} refm) (ex-gcnd gcond) (map-actionA actA)
-- ract (ee ref) = map-actionA (ract ref)
-- par (ee ref) e sys = let (a , b) = splitₚ sys
--                      in par ref e a
-- gcondInd (ee ref) e sys nsys rst ind
--   = let (a , _) = splitₚ sys
--         (na , _) = splitₚ nsys
--         in gcondInd ref e a na rst ind
-- embed (ee {refm = refm} {actA = actA} ref) e sys nsys gcnd rst
--   = let (a , b) = splitₚ sys
--         (na , nb) = splitₚ nsys
--         r = embed ref e a na gcnd rst
--         eq = split++≡id (refm a , b)
--         neq = split++≡id (refm na , nb)
--     in subst₂ (λ z w → cond actA (par ref e (proj₁ (splitₚ sys))) z
--                        ×
--                        resp actA (par ref e (proj₁ (splitₚ sys))) z w)
--               (cong proj₁ (sym eq)) ((cong proj₁ (sym neq))) r



-- cc : ∀{α} → {varsB varsA varsC : LSet {α}}
--      → {refm : System varsB → System varsA}
--      → {gcond : GCond varsB} → {act : Action varsC}
--      → RefAction (ex-refm {varsC = varsC} refm) (ex-gcnd gcond) (tmap-actionB act)
-- ract (cc {act = act}) = tmap-actionB act
-- par cc e sys = e
-- gcondInd (cc {gcond = gcond}) e sys nsys (cnd , (resp , eq)) ind = subst (λ z → gcond z) (sym (pEq⇒Eq eq)) ind
-- embed (cc {varsB = varsB} {varsA} {varsC} {refm = refm} {act = act}) e sys nsys gcnd (cnd , rsp , eq)
--   = let w = split++≡id {varsA = varsA} {varsC = varsC} (refm (proj₁ (splitₚ sys)) , proj₂ (splitₚ sys))
--         q = split++≡id {varsA = varsA} {varsC = varsC} (refm (proj₁ (splitₚ nsys)) , proj₂ (splitₚ nsys))
--     in subst₂ (λ z w → Σ (cond act e (proj₂ z)) (λ x → Σ (resp act e (proj₂ z) (proj₂ w)) (λ x₁ → (proj₁ w) ≡ (proj₁ z) all))) (sym w) (sym q) (cnd , rsp , subst (λ z → (refm (proj₁ (splitₚ nsys))) ≡ (refm z) all) (pEq⇒Eq eq) refl-all)

-- gg : ∀{α} → {varsB varsA varsC : LSet {α}}
--      → {refm : System varsB → System varsA} → {gcond : GCond varsB}
--      → {specA : Spec varsA}
--      → RSpec refm gcond specA → (specC : Spec varsC) → (ta : Bool)
--      → RSpec (ex-refm {varsC = varsC} refm) (ex-gcnd gcond) ((specA ⊔ₛ specC) ta true)
-- gg [] [] false = []
-- gg {refm = refm} {gcond} {specA = specA} [] (x ∷ specC) false
--   = {!w!} where
--   w = gg {refm = refm} {gcond} {specA = specA} [] specC false
-- gg (x ∷ rspec) specC false = {!!}
-- gg rspec specC true = {!!}

-- -- nn : ∀{α} → {varsB varsA varsC : LSet {α}} → {specB : Spec varsB} → {specA : Spec varsA}
-- --      → specB refines specA → (specC : Spec varsC) → (ta : Bool)
-- --      → ((specB ⊔ₛ specC) ta true) refines ((specA ⊔ₛ specC) ta true)
-- -- refm (nn refi specC ta) = ex-refm (refm refi)
-- -- gcond (nn refi specC ta) = ex-gcnd (gcond refi)
-- -- rspec (nn refi specC ta) = {!!}
-- -- eq (nn refi specC ta) = {!!}
