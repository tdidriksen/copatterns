{-# OPTIONS --copatterns --sized-types #-}

module Copatterns where

open import Size

record Stream {i : Size} (A : Set) : Set where
  coinductive
  constructor _::_
  field
    head : A
    tail : {j : Size< i} ->  Stream {j} A
open Stream

map : ∀ {i A B} (f : A -> B) -> (s : Stream {i} A) -> Stream {i} B
head (map {i} f s)  = f (head s)
tail (map {i} f s) {j} = map {j} f (tail s {j})

iter : {A : Set} -> (A -> A) -> A -> Stream A
head (iter f a) = a
tail (iter f a) = iter f (f a)

repeat : {A : Set} -> A -> Stream A
head (repeat a) = a
tail (repeat a) = repeat a 

data Nat : Set where
  Z : Nat
  S : Nat -> Nat

zipWith : ∀ {i : Size} {A B C : Set} -> (A -> B -> C) -> Stream {i} A -> Stream {i} B -> Stream {i} C
head (zipWith {i} f as bs) = f (head as) (head bs)
tail (zipWith {i} f as bs) {j} = zipWith {j} f (tail as {j}) (tail bs {j})

_+_ : Nat -> Nat -> Nat
_+_ Z     m = m
_+_ (S n) m = S (n + m)

_*_ : Nat -> Nat -> Nat
_*_ Z m = Z
_*_ (S n) m = m + (n * m)

nats : Stream Nat
nats = iter S Z

nats' : ∀ {i : Size} -> Stream {i} Nat
head (nats' {i})     = Z
tail (nats' {i}) {j} = map {j} S (nats' {j})

fib : ∀ {i : Size} -> Stream {i} Nat
head (fib {i})                = Z
head (tail (fib {i}) {j})     = S Z
tail (tail (fib {i}) {j}) {k} = zipWith {k} _+_ (fib {k}) (tail (fib {j}) {k})

{-
pow2 : ∀ {i : Size} ->  Stream {i} Nat
head pow2 = S Z
head (tail pow2) = S (S Z)
tail (tail pow2) = zipWith _+_ (tail pow2) (tail pow2)

-}
