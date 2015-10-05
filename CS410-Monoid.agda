module CS410-Monoid where

open import CS410-Prelude

record Monoid (M : Set) : Set where
  field
    -- OPERATIONS ----------------------------------------
    e     : M
    op    : M -> M -> M
    -- LAWS ----------------------------------------------
    lunit : forall m -> op e m == m
    runit : forall m -> op m e == m
    assoc : forall m m' m'' ->
              op m (op m' m'') == op (op m m') m''

