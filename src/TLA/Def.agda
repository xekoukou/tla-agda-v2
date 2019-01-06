module TLA.Def where


open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Unit using (⊤ ; tt)
open import Function using (case_of_)
open import Data.Sum hiding (map)
open import Data.List using (List ; _∷_ ; [] ; _++_ ; map)
open import Data.Product renaming (proj₁ to fst ; proj₂ to snd) hiding (map)
open import Data.Empty
open import Function using (id)
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Level renaming (zero to lzero ; suc to lsuc ; Lift to ℓ↑) hiding (_⊔_)

open import LTL.Core renaming ([_] to [_]ₜ)
open import LTL.Sum
open import LTL.Stateless


pattern u→_ pe = inj₂ pe
pattern _←u e  = inj₁ e


LSet : ∀{α} → Set (lsuc α)
LSet {α} = List (Set α)

V⊤ : (n : ℕ) → LSet {lzero}
V⊤ zero = []
V⊤ (suc n) = ⊤ ∷ V⊤ n

V⊤′ : ∀{α} → (n : ℕ) → LSet {α}
V⊤′ zero = []
V⊤′ (suc n) = ℓ↑ _ ⊤ ∷ V⊤′ n

VS : ∀{α} → Set α → (n : ℕ) → LSet {α}
VS A zero = []
VS A (suc n) = A ∷ VS A n

_toPS : ∀{α} → LSet {α} → Set α
_toPS (E ∷ pd) = E × (pd toPS)
_toPS [] = ℓ↑ _ ⊤


_++ₚ_ : ∀{α} → {varsA varsC : LSet {α}}
          → varsA toPS → varsC toPS → (varsA ++ varsC) toPS
_++ₚ_ {varsA = []} sys osys = osys
_++ₚ_ {varsA = x ∷ varsA} (fst , snd) osys = fst , snd ++ₚ osys

splitₚ : ∀{α} → {varsA varsC : LSet {α}} →
         (varsA ++ varsC) toPS → varsA toPS × varsC toPS
splitₚ {varsA = []} x = lift tt , x
splitₚ {varsA = _ ∷ varsA} (fst , snd) = let (a , b) = splitₚ snd
                                         in  (fst , a) , b

split++≡id : ∀{α} → {varsA varsC : LSet {α}}
     → (p : varsA toPS × varsC toPS) → splitₚ ((fst p) ++ₚ (snd p)) ≡ id p
split++≡id {varsA = []} (lift tt , snd) = refl
split++≡id {varsA = x ∷ varsA} (fs , sn) = let eq = split++≡id (snd fs , sn) in cong (λ z → ((fst fs , fst z) , snd z)) eq

_toUS : ∀{α} → LSet {α} → Set α
_toUS (E ∷ pd) = E ⊎ (pd toUS)
_toUS [] = ℓ↑ _ ⊥


split : ∀{α} → (PE : LSet {α}) → (PB : LSet {α}) → (PE ++ PB) toUS → (PE toUS) ⊎ (PB toUS)
split [] PB x = u→ x
split (E ∷ PE) PB (x ←u) = (x ←u) ←u
split (E ∷ PE) PB (u→ x)
  = case (split PE PB x) of
    λ { (x ←u) → (u→ x) ←u ; (u→ x) → u→ x}


System = _toPS

_≡_all : ∀{α} → {PE : LSet {α}} → System PE → System PE → Set α
_≡_all {PE = []} sys nsys = ℓ↑ _ ⊤
_≡_all {PE = x ∷ PE} sys nsys = fst sys ≡ fst nsys × (snd sys ≡ snd nsys all)



record Action {α} (vars : LSet {α}) : Set (lsuc α) where
  field
    E : Set α
    cond : (e : E) → (sys : System vars) → Set α
    resp : (e : E) → (sys : System vars) → (nsys : System vars) → Set α

open Action public


record ConAction {α} {vars : LSet {α}} (act : Action vars) : Set (lsuc α) where
  field
    par : System vars → (E act)
    impl : (sys : System vars) → (cnd : ((cond act) (par sys)) sys) → System vars
    safety : (sys : System vars) → (cnd : ((cond act) (par sys)) sys) → (resp act) (par sys) sys (impl sys cnd)
open ConAction public


stAction : {vars : LSet} → Action vars
E stAction = ⊤
cond stAction e sys = ⊤
resp stAction e sys nsys = nsys ≡ sys


stAction′ : ∀{α} → {vars : LSet {α}} → Action vars
E stAction′ = ℓ↑ _ ⊤
cond stAction′ e sys = ℓ↑ _ ⊤
resp stAction′ e sys nsys = nsys ≡ sys


Spec : ∀{α} → (vars : LSet {α}) → Set (lsuc α)
Spec vars = List (Action vars)

PE : ∀{α} → {vars : LSet {α}} → Spec vars → LSet {α}
PE spec = map E spec


infixr -20 _$ₛₚ_
_$ₛₚ_ : ∀{α vars} → (spec : Spec {α} vars) → (pe : (PE spec) toUS) → (sys nsys : System vars) → Set α
(act ∷ spec $ₛₚ (e ←u)) sys nsys = cond act e sys × resp act e sys nsys
(act ∷ spec $ₛₚ (u→ pe)) sys nsys = (spec $ₛₚ pe) sys nsys
([] $ₛₚ ()) sys nsys


infixr -20 _$ₛₚₜ_
_$ₛₚₜ_ : ∀{α vars} → (spec : Spec {α} vars) → (pe : ((PE spec) toUS) ʷ) → (beh : (System vars) ʷ) → (Set α) ʷ
(spec $ₛₚₜ pe) beh = ⟨ spec $ₛₚ_ ⟩ $ pe $ beh $ ○ beh


record _beh-of_ {α vars} (beh : (System vars) ʷ) (spec : Spec {α} vars) : Set α where
  field
    {pe} : ((PE spec) toUS) ʷ
    rst : [ (spec $ₛₚₜ pe) beh ]ₜ


data _≤‴_ : ℕ → ℕ → Set where
  ≤‴-refl : ∀{m} → m ≤‴ m
  ≤‴-step : ∀{m n} → suc m ≤‴ n → m ≤‴ n

≤‴⇒≤″ : ∀{m n} → m ≤‴ n → m ≤″ n
≤‴⇒≤″ {m = m} ≤‴-refl = less-than-or-equal {k = 0} (+-identityʳ m)
≤‴⇒≤″ {m = m} (≤‴-step x) = less-than-or-equal (trans (+-suc m _) (_≤″_.proof ind)) where
  ind = ≤‴⇒≤″ x



≤″⇒≤‴ : ∀{m n} → m ≤″ n → m ≤‴ n
≤″⇒≤‴ (less-than-or-equal {k} proof) = h proof where
  h : ∀{m n k} → m + k ≡ n → m ≤‴ n
  h {m} {k = zero} refl = subst (λ z → m ≤‴ z) (sym (+-identityʳ m)) (≤‴-refl {m})
  h {m} {k = suc k} proof
    = ≤‴-step (h {k = k} (trans (sym (+-suc m _)) proof))


 



line : ∀{α vars l} → (spec : Spec {α} vars)  → (pe : ⟨ (PE spec) toUS ⟩ [ 0 ,, l ⟩ )
     → (lsys : ⟨ System vars ⟩ [ 0 ,, l ] )
     → Set α
line {l = n} spec pe lsys
  = ∀ m → (l≤m : 0 ≤ m) → (m≤n : m < n)
    → (spec $ₛₚ pe m l≤m m≤n) (lsys m l≤m  (<⇒≤ m≤n)) (lsys (suc m) (≤-step l≤m) m≤n)


record SpecI {α} (vars : LSet {α}) : Set (lsuc α) where
  field
    spec : Spec vars
    init : System vars → Set α


-- Should we generalize init as above ?
-- I think we should , but let us postpone this till we need it.
record SpecI′ {α} {vars : LSet {α}} (spec : Spec vars) : Set α where
  field
    init : System vars


record _behI-of_ {α vars} (beh : (System vars) ʷ) {spec : Spec {α} vars} (speci : SpecI′ spec) : Set α where
  field
    rst : beh beh-of spec
    icnd : SpecI′.init speci ≡ ! beh


record _~>_ {α} {vars : LSet {α}} {spec : Spec vars} (speciA speciB : SpecI′ spec) : Set α where
  field
    {l} : ℕ 
    {pe} : ⟨ (PE spec) toUS ⟩ [ 0 ,, l ⟩
    {lsys} : ⟨ System vars ⟩ [ 0 ,, l ]
    ln : line spec pe lsys
    steq : SpecI′.init speciA ≡ lsys 0 z≤n z≤n
    endeq : SpecI′.init speciB ≡ lsys l z≤n ≤-refl

module _ where

open _~>_
open _beh-of_
open _behI-of_

-- A behavior of speciB can be extended with the line to form a behavior of speciA.
~>-ext : ∀{α} {vars : LSet {α}} {spec : Spec vars} {speciA speciB : SpecI′ spec} → (ar : speciA ~> speciB)
    → {beh : (System vars) ʷ} → beh behI-of speciB → []-extₛ (lsys ar) beh behI-of speciA
pe (rst (~>-ext ar behi)) = [⟩-extₛ (pe ar) (pe (rst behi))
rst (rst (~>-ext ar behi)) n with (n ≤? (l ar)) | (suc n ≤? (l ar))
rst (rst (~>-ext {spec = spec} ar behi)) n | yes p | yes q = w where
  w = subst (λ z → (spec $ₛₚ pe ar n z≤n q) (lsys ar n z≤n z) (lsys ar (suc n) z≤n q))
      (≤-irrelevance (<⇒≤ q) p) ((ln ar) n z≤n q)
rst (rst (~>-ext ar behi)) n | yes p | no ¬q with ≤-antisym p (≮⇒≥ ¬q)
rst (rst (~>-ext {spec = spec} ar {beh} behi)) .(l ar) | yes p | no ¬q | refl = u where
  t = trans (endeq ar) (cong (λ z → lsys ar (l ar) z≤n z) (≤-irrelevance ≤-refl p)) 
  w = trans (sym (icnd behi)) t
  d = cong (λ z → (spec $ₛₚ pe (rst behi) (l ar ∸ l ar)) (lsys ar (l ar) z≤n p) (beh z))
            ((+-∸-assoc 1 {l ar} {l ar} ≤-refl))
  v = trans d (cong₂ (λ z a → (spec $ₛₚ pe (rst behi) z) a
                (beh (suc z))) (n∸n≡0 (l ar)) (sym w))
  u = subst (λ z → z) (sym v) (rst (rst behi) 0)
rst (rst (~>-ext ar behi)) n | no ¬p | yes q = ⊥-elim (<-asym q e) where
  e = ≰⇒> ¬p
rst (rst (~>-ext {spec = spec} ar {beh} behi)) n | no ¬p | no ¬q
  = subst (λ z → (spec $ₛₚ pe (rst behi) (n ∸ l ar)) (beh (n ∸ l ar)) (beh z))
          (sym (+-∸-assoc 1 {n} {l ar} (≰⇒≥ ¬p))) (rst (rst behi) (n ∸ l ar))
icnd (~>-ext ar behi) = steq ar



-- Any map can be used to apply a spec to the domain of that mapping.
-- Obviously the new spec refines the original and if the map is a bijection, then
-- it is a SpecEquality.

map-act : ∀{α} → {varsA varsB : LSet {α}} → (f : System varsB → System varsA)
    → Action varsA → Action varsB
E (map-act f x) = E x
cond (map-act f x) e sys = cond x e (f sys)
resp (map-act f x) e sys nsys = resp x e (f sys) (f nsys)

map-spec : ∀{α} → {varsA varsB : LSet {α}} → Spec varsA
    → (f : System varsB → System varsA) → Spec varsB
map-spec x f = map (map-act f) x
