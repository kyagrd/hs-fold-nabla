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

data Tm = Var Nm
        | Lam (Bind Nm Tm)
        | App Tm Tm
     deriving (Eq,Ord,Show)

data Ty = Prop
        | Unit
        | Arr Ty Ty
        deriving (Eq,Ord,Show)

data Form
  = Forall(Bind (Nm,Embed Ty) Form)
  | Exists(Bind (Nm,Embed Ty) Form)
  | Nabla (Bind (Nm,Embed Ty) Form)
  | Imply Form Form
  | Conj Form Form
  | Disj Form Form
  | Equ Tm Tm
  deriving (Eq,Ord,Show)

type Sig = [(Nm,Embed Ty)]
type Judgment = Bind Sig Form
type Sequent = Bind Sig ([Judgment], Judgment)

instance Eq (Bind Nm Tm) where (==) = aeq
instance Ord (Bind Nm Tm) where compare = acompare

instance Eq (Bind (Nm,Embed Ty) Form) where (==) = aeq
instance Ord (Bind (Nm,Embed Ty) Form) where compare = acompare

$(derive [''Tm,''Ty,''Form])

instance Alpha Ty
instance Alpha Tm
instance Alpha Form

instance Subst Tm Tm where
  isvar (Var x) = Just (SubstName x)
  isvar _       = Nothing
instance Subst Tm Ty where
instance Subst Tm Form where


lam x = Lam . bind x
app = App

occurs :: Alpha t => Nm -> t -> Bool
occurs x t = x `elem` (fv t :: [Nm])
