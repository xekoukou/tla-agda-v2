module TLA.Lemmas where

open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding (sym)
open import Relation.Nullary
open import Data.Empty
open import Data.Unit hiding (_≤_)
open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Fin hiding (_≤_)
open import Function.Inverse hiding (sym)
open import Data.Fin.Permutation
open import TLA.Def
open import TLA.Refine
open import Data.List hiding (tabulate ; lookup)
open import Data.Vec
open import Data.Sum
open import Data.Product
open import Level renaming (zero to lzero ; suc to lsuc)

