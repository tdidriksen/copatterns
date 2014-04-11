data nat = {Z | S nat}

data natList = {nil | cons nat natList}

codata natStream = {head nat | tail natStream}

let plus (n : nat, m : nat) : (nat -> nat -> nat) = 
  case n : nat of 
      Z -> m ; 
      S n' -> plus (n', m)

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