{-# OPTIONS --copatterns #-}

module Copatterns where

record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A
open Stream

map : {A B : Set} -> (A -> B) -> Stream A -> Stream B
head (map f as) = f (head as)
tail (map f as) = map f (tail as)

iter : {A : Set} -> (A -> A) -> A -> Stream A
head (iter f a) = a
tail (iter f a) = iter f (f a)

data Nat : Set where
  Z : Nat
  S : Nat -> Nat

zipWith : {A B C : Set} -> (A -> B -> C) -> Stream A -> Stream B -> Stream C
head (zipWith f as bs) = f (head as) (head bs)
tail (zipWith f as bs) = zipWith f (tail as) (tail bs)

_+_ : Nat -> Nat -> Nat
_+_ Z     m = m
_+_ (S n) m = S (n + m)

_*_ : Nat -> Nat -> Nat
_*_ Z m = Z
_*_ (S n) m = m + (n * m)

nats : Stream Nat
nats = iter S Z

fib : Stream Nat
head fib        = Z
head (tail fib) = S Z
tail (tail fib) = zipWith _+_  fib (tail fib)

pow2 : Stream Nat
head pow2 = S Z
head (tail pow2) = S (S Z)
tail (tail pow2) = zipWith _+_ (tail pow2) (tail pow2)

