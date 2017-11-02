{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE UndecidableInstances      #-}

module Syntax    where

import           Unbound.LocallyNameless

type Nm = Name Tm

data Tm = V Nm
        | B Nm
        | Lam (Bind Nm Tm)
        | App Tm Tm
     deriving (Eq,Ord,Show)

instance Eq (Bind Nm Tm) where (==) = aeq
instance Ord (Bind Nm Tm) where compare = acompare

$(derive [''Tm])

instance Alpha Tm

instance Subst Tm Tm where
  isvar (V x) = Just (SubstName x)
  isvar (B x) = Just (SubstName x)
  isvar _     = Nothing

lam x = Lam . bind x
app = App

occurs :: Alpha t => Nm -> t -> Bool
occurs x t = x `elem` (fv t :: [Nm])
