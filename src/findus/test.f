data nat = {Z | S nat}

data natList = {nil | cons nat natList}

codata natStream = {head nat | tail natStream}

let plus (n : nat, m : nat) : (nat -> nat -> nat) = 
  case n : nat of 
      Z -> m ; 
      S n' -> plus (n', m)

let pred (n : nat) : (nat -> nat) =
  case n : nat of
    Z -> Z ;
    S n' -> n'

let natListTail (xs : natList) : (natList -> natList) =
  case xs : natList of
    nil -> nil ;
    cons x xs -> xs

let zipStreamWithPlus (xs : natStream, ys : natStream) : (natStream -> natStream -> natStream) = 
  observe natStream as 
    head -> plus (head (xs), head (ys)) ;
    tail -> zipStreamWithPlus (tail (xs), tail (ys))

let fib : natStream = 
  observe natStream as
    head -> Z ;
    tail -> observe natStream as
              head -> S (Z) ;
              tail -> zipStreamWithPlus (fib, tail (fib))

let zeros : natStream =
  observe natStream as
    head -> Z ;
    tail -> zeros


-- Mutual recursion test
let stupid1 (n : nat) : (nat -> nat) = stupid2 (n)
let stupid2 (n : nat) : (nat -> nat) = stupid1 (n)

-- Infinite
let inf (n : nat) : (nat -> nat) = inf (n)