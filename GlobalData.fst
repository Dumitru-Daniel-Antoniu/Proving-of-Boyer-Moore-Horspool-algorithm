module GlobalData

open FStar.Classical 
open FStar.IO
open FStar.Printf
open FStar.List
open FStar.List.Tot.Base

type english_letters =
  | A
  | B

val alphabet : (l:list english_letters{(forall (x:english_letters). mem x l = true) /\ l <> []})
let alphabet = [A;B]
  
val text : (l:list english_letters{l <> []})
let text = [A;A;A;A;B;A;A;B;A;B;A;A;A;B;A;B;B]

let rec l1_length_less_than_l2_length (l1:list english_letters) (l2:list english_letters)
  : bool
  = if length l1 > 0 && length l2 > 0 
    then l1_length_less_than_l2_length (tail l1) (tail l2)
    else (
      if length l1 = 0 
      then true
      else false
    )

let rec l1_less_true (l1:list english_letters) (l2:list english_letters)
  : Lemma (requires l1_length_less_than_l2_length l1 l2 = true)
          (ensures length l1 <= length l2)
  = if length l1 > 0 && length l2 > 0 
    then l1_less_true (tail l1) (tail l2)
    else ()

let rec l1_less_false (l1:list english_letters) (l2:list english_letters)
  : Lemma (requires l1_length_less_than_l2_length l1 l2 = false)
          (ensures length l1 > length l2)
  = if length l1 > 0 && length l2 > 0 
    then l1_less_false (tail l1) (tail l2)
    else ()

let candidate : list english_letters 
  = [A;A;B;A;A;A;B;A;B]

val pattern : (l:list english_letters{length l <= length text})
let pattern = if l1_length_less_than_l2_length candidate text = true
              then (
                l1_less_true candidate text;
                candidate
              )
              else []