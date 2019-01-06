module TLA.DefProp where

open import Data.List
open import Data.Product hiding (map)
open import Data.Bool
open import TLA.Def




-- Only two maps are needed , and the other should be determined through an isomorphism determined through permutation.
-------------------------------------------------


-- maping an action field across different spaces.
-- The condition does not add new restrictions, thus it fills the whole space.
-- The response can have restrictions that make the action tangent to the embedded space.
-- or not, and thus permit changes of the new variables.

map-cndA : ∀{α} → {varsA : LSet {α}} → {varsB : LSet {α}}
       → ((sys : System varsA) → Set α) → ((sys : System (varsA ++ varsB)) → Set α)
map-cndA cnd sys = let (a , _) = splitₚ sys
                   in cnd a

map-cndB : ∀{α} → {varsA : LSet {α}} → {varsB : LSet {α}}
       → ((sys : System varsB) → Set α) → ((sys : System (varsA ++ varsB)) → Set α)
map-cndB cnd sys = let (_ , b) = splitₚ sys
                   in cnd b


-- tangent maping of response.
tmap-respA : ∀{α} → {varsA : LSet {α}} → {varsB : LSet {α}}
       → ((sys nsys : System varsA) → Set α) → ((sys nsys : System (varsA ++ varsB)) → Set α)
tmap-respA resp sys nsys = let (a , b) = splitₚ sys
                               (na , nb) = splitₚ nsys
                           in resp a na × (nb ≡ b all)


-- tangent maping of response.
tmap-respB : ∀{α} → {varsA : LSet {α}} → {varsB : LSet {α}}
       → ((sys nsys : System varsB) → Set α) → ((sys nsys : System (varsA ++ varsB)) → Set α)
tmap-respB resp sys nsys = let (a , b) = splitₚ sys
                               (na , nb) = splitₚ nsys
                           in resp b nb × (na ≡ a all)


map-respA : ∀{α} → {varsA : LSet {α}} → {varsB : LSet {α}}
       → ((sys nsys : System varsA) → Set α) → ((sys nsys : System (varsA ++ varsB)) → Set α)
map-respA resp sys nsys = let (a , b) = splitₚ sys
                              (na , nb) = splitₚ nsys
                          in resp a na


map-respB : ∀{α} → {varsA : LSet {α}} → {varsB : LSet {α}}
       → ((sys nsys : System varsB) → Set α) → ((sys nsys : System (varsA ++ varsB)) → Set α)
map-respB resp sys nsys = let (a , b) = splitₚ sys
                              (na , nb) = splitₚ nsys
                          in resp b nb




tmap-actionA : ∀{α} → {varsA : LSet {α}} → {varsB : LSet {α}}
       → Action varsA → Action (varsA ++ varsB)
E (tmap-actionA act) = E act
cond (tmap-actionA act) e = map-cndA (cond act e)
resp (tmap-actionA act) e = tmap-respA (resp act e)

tmap-actionB : ∀{α} → {varsA : LSet {α}} → {varsB : LSet {α}}
       → Action varsB → Action (varsA ++ varsB)
E (tmap-actionB act) = E act
cond (tmap-actionB act) e = map-cndB (cond act e)
resp (tmap-actionB act) e = tmap-respB (resp act e)

map-actionA : ∀{α} → {varsA : LSet {α}} → {varsB : LSet {α}}
       → Action varsA → Action (varsA ++ varsB)
E (map-actionA act) = E act
cond (map-actionA act) e = map-cndA (cond act e)
resp (map-actionA act) e = map-respA (resp act e)

map-actionB : ∀{α} → {varsA : LSet {α}} → {varsB : LSet {α}}
       → Action varsB → Action (varsA ++ varsB)
E (map-actionB act) = E act
cond (map-actionB act) e = map-cndB (cond act e)
resp (map-actionB act) e = map-respB (resp act e)


-- Bools determine if the mapping is tangent or not.
-- To be removed.
_⊔ₛ_ : ∀{α} → {varsA varsB : LSet {α}} → Spec varsA → Spec varsB
       → Bool → Bool → Spec (varsA ++ varsB)
(specA ⊔ₛ specB) false false = map map-actionA specA ++ map map-actionB specB
(specA ⊔ₛ specB) false true = map map-actionA specA ++ map tmap-actionB specB
(specA ⊔ₛ specB) true false = map tmap-actionA specA ++ map map-actionB specB
(specA ⊔ₛ specB) true true = map tmap-actionA specA ++ map tmap-actionB specB
