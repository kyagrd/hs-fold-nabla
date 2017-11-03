{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE StandaloneDeriving        #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE UndecidableInstances      #-}

module Syntax    where

import           Unbound.LocallyNameless
import           Unbound.LocallyNameless.Ops

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
  | TT
  | FF
  | A String [Tm]
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

lvl :: [(String,Int)] -> Form -> Int
lvl _ TT             = 0
lvl _ FF             = 0
lvl lvp (A p _)      = k where Just k = lookup p lvp
lvl lvp (Imply f1 f2) = max (1 + lvl lvp f1) (lvl lvp f2)
lvl lvp (Conj f1 f2) = max (lvl lvp f1) (lvl lvp f2)
lvl lvp (Disj f1 f2) = max (lvl lvp f1) (lvl lvp f2)
lvl lvp (Forall b)   = lvl lvp (snd $ unsafeUnbind b)
lvl lvp (Exists b)   = lvl lvp (snd $ unsafeUnbind b)
lvl lvp (Nabla b)    = lvl lvp (snd $ unsafeUnbind b)
