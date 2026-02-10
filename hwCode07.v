

(*
  Nobody has complained, so the
   exam dates are fixed:

     2025-05-14, Wednesday, 12:00

  Retake:

     2025-05-21, Wednesday, 12:00
*)


(*
Please write me an email, when do you want to
come for consultation, and I will write it into
the timeslots.txt file.
Possible times: next Tuedsday, Thursday, Friday
(25th, 27th, 28th of March).
*)




(*Homework for week07. Deadline:
  2025-03-23, Sunday, but you can still
  get less and less points until Friday*)

Require Import Week07.lib07.
Require Import List.


Definition init A: list A->list A.
(*From classwork: removes the last element if any
and returns the remaining list*)
refine(
fix F l:=
match l with
  |  nil => nil
  |  cons data smallerlist =>
  match smallerlist with
    | nil => nil
    | cons data2 evensmallerlist =>
        data :: (F smallerlist)
  end
end
).
Defined.



(*snoc puts a new element
  to the end of the list*)
Definition snoc A: list A -> A -> list A.
refine(
fix F l a:=
   match l with
  | nil => a :: nil
  | cons x xs => x :: (F xs a)
  end
 (*write your solution here*)
).
Defined. (* <- change this to Defined when finished *)



(*the reverse function reverses the list,
i.e puts the elements into backwards order.*)
Definition reverse A: list A -> list A.
refine(
fix F l:=
 match l with
  | nil => nil
  | cons x xs => (F xs) ++ (x :: nil)
  end
(*write your solution here*)
).
Defined. (* <- change this to Defined when finished *)



(* append concatenates two lists *)
Definition append A: list A -> list A -> list A.
refine(
fix F l1 l2 :=
 match l1 with
  | nil => l2
  | cons x xs => x :: (F xs l2)
  end (*write your solution here*)
).
Defined. (* <- change this to Defined when finished *)


(*zip takes two lists and create a list of
pairs of the elements of the input lists
(see the test). It stops when the sorter
list ends
For example zip nat nat (1::2::nil) (3::4::nil) =
              (1,3)::(2,4)::nil
*)
Definition zip A B: list A -> list B -> list (A*B).
refine(
fix F l1 l2 :=
match l1, l2 with
  | nil, _ | _, nil => nil
  | cons h1 t1, cons h2 t2 => (h1, h2) :: (F t1 t2)
end(*write your solution here*)
).
Defined. (* <- change this to Defined when finished *)

(*unzip is he opposite of zip, it takes
a list of pairs and separates them into two lists*)
Definition unzip A B: list (A*B) -> list A*list B.
refine(
fix F l :=
match l with
  | nil => (nil, nil)
  | cons (a, b) t =>
      let (la, lb) := F t in (a :: la, b :: lb)
end(*write your solution here*)
).
Defined. (* <- change this to Defined when finished *)



(*Only keeps the odd elements of the list,
 deletes the even ones*)
Definition oddElements A: list A -> list A.
refine(
fix F l :=
 match l with
  | nil => nil
  | cons h t => h :: t
end(*write your solution here*)
).
Defined. (* <- change this to Defined when finished *)

(*Only keeps the even elements of the list,
 deletes the odd ones*)
Definition evenElements A: list A -> list A.
refine(
fix F l :=
match l with
  | nil => nil
  | cons _ t => t
end(*write your solution here*)
).
Defined. (* <- change this to Defined when finished *)

(*The combination of the above two.
For example:
oddEvenElementsSplit student
    [Alice;Bob;Charlie] = ([Alice;Charlie],[Bob]).
*)
(*
Definition oddEvenElementsSplit A:
   list A -> list A*list A.
refine(
fix F l := fix F l := (oddElements l, evenElements l)(*write your solution here*)
).
Defined. (* <- change this to Defined when finished *)
*)
(*Joins the two lists, puts the first list into
even positions, the second one into even positions.
Stops when the shorter list runsout of elements.*)
Definition intersparse A:
   list A -> list A -> list A.
refine(
fix F l1 l2 :=
match l1, l2 with
  | nil, _ => l2
  | _, nil => l1
  | cons h1 t1, cons h2 t2 => h1 :: h2 :: (F t1 t2)
end(*write your solution here*)
).
Defined. (* <- change this to Defined when finished *)

(*Applies a function of two inputs to the
  elements of two lists. Stops, when the shorter
  list ends. For example:
map2 nat nat nat add (1::2::3::nil) (4::5::nil) (5::7::nil)
*)
Definition map2 A B C:
   (A->B->C) -> list A -> list B -> list C.
refine(
fix F f l1 l2 :=
match l1, l2 with
  | nil, _ | _, nil => nil
  | cons h1 t1, cons h2 t2 => (f h1 h2) :: (F f t1 t2)
end(*write your solution here*)
).
Defined. (* <- change this to Defined when finished *)

(*takes a list of lists and concatenates
the elements. For example:
flatten nat ((1::2::nil)::(3::4::nil)::(5::6::7::nil)::nil) =
    (1::2::3::4::5::6::7::nil *)
Definition flatten A: list (list A) -> list A.
refine(
fix F ll :=
  match ll with
    | nil => nil
    | cons h t => h ++ (F t)
  end(*write your solution here*)
).
Defined. (* <- change this to Defined when finished *)


(*Keep only every nth element of a list. For example:
keepNth nat 3 (1::2::3::4::5::6::7::nil) = (3::6::nil)
*)
(*
Definition keepNth A: nat -> list A -> list A.
refine(
fix F n l :=
  match l with
    | nil => nil
    | cons h t => match n with
                    | 1 => h :: keepNth n t
                    | S n' => keepNth n' t
                  end
  end
(*write your solution here*)
).
Defined. (* <- change this to Defined when finished *)

(*Deletes every nth element of a list For example:
deleteNth nat 3 (1::2::3::4::5::6::7::nil) = (1::2::4::5::7::nil)
*)
Definition deleteNth A: nat -> list A -> list A.
refine(
fix F n l :=
  match l with
  | nil => nil
  | cons h t => match n with
                  | 1 => deleteNth n t
                  | S n' => h :: deleteNth n' t
                end
end
(*write your solution here*)
).
Defined. (* <- change this to Defined when finished *)
*)

(*Difficult exercises for advanced students*)
(*We have learned one representation of the natural numbers,
where each number contains the number one less. In this
case the numbers look like this:

0 <- 1 <- 2 <- 3 <- 4 ....

(the arrow means containment).
There are other possibilities, for example we can
organize the numbers into a tree:

                 0
              /     \
             1       2
            / \     / \
           3   4   5   6

in this case both 1 and 2 contains 0, so we need to distinguish
between them.  It can be done with the following datatype:
*)
Inductive bnat:=
  | bZ
  | bL (n:bnat)  (*we move left in the tree*)
  | bR (n:bnat). (*we move right in the tree*)

(*in this case the first few numbers:
  0 = bZ
  1 = bL bZ
  2 = bR bZ
  3 = bL (bL bZ)
  4 = bR (bL bZ)
  5 = bL (bR bZ)
  6 = bR (bR bZ)

so the value of  (bL n)  is 2n+1, the value of
 (bR n) is 2n+2, where n is the number inside.

*)


(*The successor function, it add one to the input*)
Definition succ: bnat->bnat.
refine(
fix F n :=
match n with
  | bZ => bL bZ
  | bL x => bR x
  | bR x => bL (F x)
end
).
Defined.



(*The predecessor function, it substracts one from the input.
  If the input is zero, the output is also zero.*)
Definition pred: bnat->bnat.
refine(
fix F n :=
match n with
  | bZ => bZ
  | bL x => match x with
              | bZ => bZ
              | _ => bR (F x)
            end
  | bR x => bL x
end
).
Defined.
(*
(*Addition. You can use succ, if needed.*)
Definition badd: bnat->bnat->bnat.
refine(
fix F n m :=
match m with
  | bZ => n
  | _ => F (succ n) (pred m)
end
).
Defined.


(*Conversion functions between nat and bnat.
  They should be the inveses of each other.*)

Definition nat2bnat: nat->bnat.
refine(
fix F n :=
match n with
  | bZ => 0
  | _ => 1 + (F (pred n))
end
).
Defined.

*)

