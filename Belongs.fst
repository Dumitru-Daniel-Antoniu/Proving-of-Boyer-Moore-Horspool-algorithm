module Belongs

open UpdateBc
open GlobalData
open ItemIndices
open NewOrOld
open FStar.Classical 
open FStar.IO
open FStar.Printf
open FStar.List
open FStar.List.Tot.Base

let rec belongs (t:list english_letters) (p:list english_letters{length p <= length t}) (i:nat)
  : bool 
  = match p with
    | [] -> true
    | hd :: tl -> if i < length t && hd = index t i 
                  then belongs t tl (i + 1)
                  else false

let rec belongs_true_index_is_equal_base (t:list english_letters) (p:list english_letters{length p <= length t}) (i:nat{i <= length t - length p}) (j:nat{j >= i && j < i + length p})
  : Lemma (ensures belongs t p i = true ==> index t j = index p (j - i))
  = match p with 
    | [] -> ()
    | hd :: tl -> if hd = index t i 
                  then (
                    assert(belongs t p i = belongs t tl (i + 1));
                    if i < j 
                    then belongs_true_index_is_equal_base t tl (i + 1) j
                    else ()
                  )
                  else ()

let belongs_true_indices_are_equal (t:list english_letters) (p:list english_letters{length p <= length t})
  : Lemma (ensures forall (i:nat{i <= length t - length p}) (j:nat{j >= i && j < i + length p}). belongs t p i = true ==> index t j = index p (j - i))
  = forall_intro_2 (belongs_true_index_is_equal_base t p)

let rec belongs_false_index_is_not_equal_base (t:list english_letters) (p:list english_letters{length p <= length t}) (i:nat{i <= length t - length p}) 
  : Lemma (ensures belongs t p i = false ==> (exists (j:nat{j >= i && j < i + length p}). index t j <> index p (j - i)))
  = match p with 
    | [] -> ()
    | hd :: tl -> if hd = index t i 
                  then belongs_false_index_is_not_equal_base t tl (i + 1)
                  else ()

let belongs_false_index_is_not_equal (t:list english_letters) (p:list english_letters{length p <= length t})
  : Lemma (ensures forall (i:nat{i <= length t - length p}) . belongs t p i = false ==> (exists (j:nat{j >= i && j < i + length p}). index t j <> index p (j - i)))
  = forall_intro (belongs_false_index_is_not_equal_base t p)

let rec index_is_not_equal_belongs_false_base (t:list english_letters) (p:list english_letters{length p <= length t}) (i:nat{i <= length t - length p})
  : Lemma (ensures (exists (j:nat{j >= i && j < i + length p}). index t j <> index p (j - i)) ==> belongs t p i = false)
  = match p with 
    | [] -> ()
    | hd :: tl -> if hd <> index t i
                  then ()
                  else index_is_not_equal_belongs_false_base t tl (i + 1)

let index_is_not_equal_belongs_false (t:list english_letters) (p:list english_letters{length p <= length t}) 
  : Lemma (ensures forall (i:nat{i <= length t - length p}). (exists (j:nat{j >= i && j < i + length p}). index t j <> index p (j - i)) ==> belongs t p i = false)
  = forall_intro (index_is_not_equal_belongs_false_base t p)

let rec indices_are_equal_belongs_true_base (t:list english_letters) (p:list english_letters{length p <= length t}) (i:nat{i <= length t - length p})
  : Lemma (ensures (forall (j:nat{j >= i && j < i + length p}). index t j = index p (j - i)) ==> belongs t p i = true)
  = match p with 
    | [] -> ()
    | hd :: tl -> if hd <> index t i 
                  then ()
                  else indices_are_equal_belongs_true_base t tl (i + 1)

let indices_are_equal_belongs_true (t:list english_letters) (p:list english_letters{length p <= length t})
  : Lemma (ensures forall (i:nat{i <= length t - length p}). (forall (j:nat{j >= i && j < i + length p}). index t j = index p (j - i)) ==> belongs t p i = true)
  = forall_intro (indices_are_equal_belongs_true_base t p)

let maximum (a:int) (b:int)
  : int 
  = if a > b 
    then a 
    else b 

let maximum_returns_correct_result_base (a:int) (b:int)
  : Lemma (ensures maximum a b = a ==> a >= b)
  = ()

let maximum_returns_correct_result ()
  : Lemma (ensures forall (a:int) (b:int). maximum a b = a ==> a >= b)
  = forall_intro_2 maximum_returns_correct_result_base

let minimum (a:int) (b:int)
  : int 
  = if a > b 
    then b 
    else a 

let minimum_returns_correct_result_base (a:int) (b:int)
  : Lemma (ensures minimum a b = a ==> a <= b)
  = ()

let minimum_returns_correct_result ()
  : Lemma (ensures forall (a:int) (b:int). minimum a b = a ==> a <= b)
  = forall_intro_2 minimum_returns_correct_result_base