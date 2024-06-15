module ProvingItemIndex 

open FStar.Classical 
open FStar.IO
open FStar.Printf
open FStar.List
open FStar.List.Tot.Base

type english_letters =
  | A
  | B
  // | C 
  // | D
  // | E
  // | F 
  // | G
  // | H
  // | I 
  // | J
  // | K
  // | L 
  // | M 
  // | N 
  // | O 
  // | P 
  // | Q 
  // | R 
  // | S 
  // | T 
  // | U 
  // | V 
  // | W 
  // | X 
  // | Y 
  // | Z

val alphabet : (l:list english_letters{(forall (x:english_letters). mem x l = true) /\ l <> []})
let alphabet = [A;B]//;C;D;E;F;G;H;I;J;K;M;N;O;P;Q;R;S;T;U;V;W;X;Y;Z]
  
val text : (l:list english_letters{l <> []})
let text = [A;A;A;A;B;A;A;B;A;B;A;A;A;B;A;B;B]

val pattern : (l:list english_letters{length l <= length text})
let pattern = [A;B;B]

val alphabet_length : (i:nat{i > 0})
let alphabet_length = length alphabet

let rec create_bc (i:nat) : Tot (list int) (decreases i) 
  =match i with
      | 0 -> []
      | _ -> (-1) :: (create_bc (i-1))

let rec length_create_bc_is_positive (i:nat)
  : Lemma (ensures length (create_bc i) >= 0)
  = match i with
    | 0 -> ()
    | _ -> length_create_bc_is_positive (i - 1)

let rec length_create_bc_is_i (i:nat) :
   Lemma (ensures (length (create_bc i) = i)) =
   match i with 
     | 0 -> ()
     | _ -> length_create_bc_is_i (i - 1)

let rec index_n_bc_is_minusone (i:nat) :
  Lemma (ensures 
        (let l = (create_bc i) in 
         forall (n:nat). n < length l ==> index l n = -1))
  = match i with
    | 0 -> ()
    | _ -> index_n_bc_is_minusone (i - 1)

let bc : list int = create_bc alphabet_length

let bc_length_is_positive = length_create_bc_is_positive alphabet_length
let bc_length_is_alphabet = length_create_bc_is_i alphabet_length
let bc_nth_element_is_minusone = index_n_bc_is_minusone alphabet_length

//indices
val item_index (#a:eqtype) (item:a) (l:list a) (i:nat) : list nat
let rec item_index item l i
  = match l with 
    | [] -> []
    | hd :: tl -> if hd = item
                  then i :: item_index item tl (i + 1)
                  else item_index item tl (i + 1)

let rec item_list_has_correct_length (#a:eqtype) (l:list a) (i:nat)
  : Lemma (ensures forall (item:a). length (item_index item l i) = count item l)
  = match l with 
    | [] -> ()
    | hd :: tl -> item_list_has_correct_length tl (i + 1)

let rec item_indices_is_in_interval (#a:eqtype) (item:a) (l:list a) (i:nat) (x:nat)
  : Lemma (ensures mem x (item_index item l i) ==> i <= x && x < i + length l)
  = match l with 
    | [] -> () 
    | hd :: tl -> item_indices_is_in_interval item tl (i + 1) x 

let item_indices_is_in_interval_forall (#a:eqtype) (item:a) (l:list a) (i:nat)
  : Lemma (ensures forall (x:nat). mem x (item_index item l i) ==> i <= x && x < i + length l)
  = forall_intro (item_indices_is_in_interval item l i)

let rec item_indices_one_and_item_indices_zero (#a:eqtype) (item:a) (l:list a) (x:nat{x > 0}) (i:nat{i > 0})
  : Lemma (ensures mem x (item_index item l i) = mem (x - 1) (item_index item l (i - 1)))
  = match l with 
    | [] -> ()
    | hd :: tl -> match x with 
                  | 1 -> if i = 1
                         then (
                          if hd = item 
                          then ()
                          else (
                           item_indices_is_in_interval item tl (i + 1) x;
                           item_indices_is_in_interval item tl i (x - 1)
                          )
                         )
                         else (
                           item_indices_is_in_interval item l i x;
                           item_indices_is_in_interval item l (i - 1) (x - 1)
                         )
                  | _ -> if i > x
                         then (
                          item_indices_is_in_interval item l i x;
                          item_indices_is_in_interval item l (i - 1) (x - 1)
                         )
                         else (
                          if i = x 
                          then (
                            if hd = item 
                            then ()
                            else (
                             item_indices_is_in_interval item tl (i + 1) x;
                             item_indices_is_in_interval item tl i (x - 1)
                            )
                          )
                          else (
                            assert(mem x (item_index item l i) = mem x (item_index item tl (i + 1)));
                            assert(mem (x - 1) (item_index item l (i - 1)) = mem (x - 1) (item_index item tl i));
                            item_indices_one_and_item_indices_zero item tl x (i + 1)
                          )
                         )

let rec index_increases_with_one_when_element_is_added (#a:eqtype) (item:a) (l:list a) (i:nat{i > 0}) (el:a)
  : Lemma (ensures mem (i - 1) (item_index item l 0) = false ==> mem i (item_index item (el :: l) 0) = false)
  = match l with 
    | [] -> ()
    | hd :: tl -> match i with 
                  | 1 -> if hd = item 
                         then ()
                         else item_indices_is_in_interval item tl 2 1
                  | _ -> item_indices_one_and_item_indices_zero item l i 1;
                         index_increases_with_one_when_element_is_added item tl (i - 1) hd

let rec index_increases_with_one_when_element_is_added_for_true (#a:eqtype) (item:a) (l:list a) (i:nat{i > 0}) (el:a)
  : Lemma (ensures mem (i - 1) (item_index item l 0) = true ==> mem i (item_index item (el :: l) 0) = true)
  = match l with 
    | [] -> ()
    | hd :: tl -> match i with 
                  | 1 -> if hd = item 
                         then ()
                         else item_indices_is_in_interval item tl i (i - 1)
                  | _ -> item_indices_one_and_item_indices_zero item l i 1;
                         index_increases_with_one_when_element_is_added_for_true item tl (i - 1) hd

let rec index_increases_with_one_when_first_is_item (#a:eqtype) (item:a) (l:list a) (i:nat{i > 0})
  : Lemma (ensures mem (i - 1) (item_index item l 0) = false ==> mem i (0 :: item_index item l 1) = false)
  = match l with 
    | [] -> ()
    | hd :: tl -> match i with 
                  | 1 -> if hd = item 
                         then ()
                         else item_indices_is_in_interval item tl 2 1
                  | _ -> item_indices_one_and_item_indices_zero item l i 1;
                         index_increases_with_one_when_first_is_item item tl (i - 1)

let rec index_increases_with_one_when_first_is_item_for_true (#a:eqtype) (item:a) (l:list a) (i:nat{i > 0})
  : Lemma (ensures mem (i - 1) (item_index item l 0) = true ==> mem i (0 :: item_index item l 1) = true)
  = match l with 
    | [] -> ()
    | hd :: tl -> match i with 
                  | 1 -> if hd = item 
                         then ()
                         else item_indices_is_in_interval item tl i (i - 1)
                  | _ -> item_indices_one_and_item_indices_zero item l i 1;
                         index_increases_with_one_when_first_is_item_for_true item tl (i - 1)

let rec index_is_not_item_is_not_mem_base (#a:eqtype) (l:list a) (item:a) (i:nat{i < length l})
  : Lemma (ensures index l i <> item ==> mem i (item_index item l 0) = false)
  = match l with
    | [] -> ()
    | hd :: tl -> match i with 
                  | 0 -> if hd = item 
                         then ()
                         else item_indices_is_in_interval item tl (i + 1) i
                  | _ -> if hd = item 
                         then index_increases_with_one_when_first_is_item item tl i
                         else index_increases_with_one_when_element_is_added item tl i hd;
                         index_is_not_item_is_not_mem_base tl item (i - 1)

let index_is_not_item_is_not_mem (#a:eqtype) (l:list a) 
  : Lemma (ensures forall (item:a) (i:nat{i < length l}). index l i <> item ==> mem i (item_index item l 0) = false)
  = forall_intro_2 (index_is_not_item_is_not_mem_base l)

let rec index_is_item_is_mem_base (#a:eqtype) (l:list a) (item:a) (i:nat{i < length l})
  : Lemma (ensures index l i = item ==> mem i (item_index item l 0) = true)
  = match l with
    | [] -> ()
    | hd :: tl -> match i with 
                  | 0 -> if hd = item
                         then ()
                         else item_indices_is_in_interval item tl (i + 1) i
                  | _ -> assert(index l i = index tl (i - 1));
                         if hd = item
                         then index_increases_with_one_when_first_is_item_for_true item tl i 
                         else index_increases_with_one_when_element_is_added_for_true item tl i hd;
                         index_is_item_is_mem_base tl item (i - 1)

let index_is_item_is_mem (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a) (i:nat{i < length l}). index l i = item ==> mem i (item_index item l 0) = true)
  = forall_intro_2 (index_is_item_is_mem_base l)

let rec index_is_not_mem_is_not_item_base (#a:eqtype) (l:list a) (item:a) (i:nat{i < length l})
  : Lemma (ensures mem i (item_index item l 0) = false ==> index l i <> item)
  = match l with
    | [] -> ()
    | hd :: tl -> match i with 
                  | 0 -> if hd = item 
                         then ()
                         else item_indices_is_in_interval item tl (i + 1) i
                  | _ -> index_is_not_mem_is_not_item_base tl item (i - 1);
                         item_indices_one_and_item_indices_zero item tl i 1

let index_is_not_mem_is_not_item_forall_i (#a:eqtype) (l:list a) (item:a)
  : Lemma (ensures forall (i:nat{i < length l}). mem i (item_index item l 0) = false ==> index l i <> item)
  = forall_intro (index_is_not_mem_is_not_item_base l item)

let index_is_not_mem_is_not_item (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a) (i:nat{i < length l}). mem i (item_index item l 0) = false ==> index l i <> item)
  = forall_intro (index_is_not_mem_is_not_item_forall_i l)

let rec index_is_mem_is_item_base (#a:eqtype) (l:list a) (item:a) (i:nat{i < length l})
  : Lemma (ensures mem i (item_index item l 0) = true ==> index l i = item)
  = match l with
    | [] -> ()
    | hd :: tl -> match i with 
                  | 0 -> if hd = item 
                         then ()
                         else item_indices_is_in_interval item tl (i + 1) i
                  | _ -> index_is_mem_is_item_base tl item (i - 1);
                         item_indices_one_and_item_indices_zero item tl i 1

let index_is_mem_is_item_forall_i (#a:eqtype) (l:list a) (item:a)
  : Lemma (ensures forall (i:nat{i < length l}). mem i (item_index item l 0) = true ==> index l i = item)
  = forall_intro (index_is_mem_is_item_base l item)

let index_is_mem_is_item (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a) (i:nat{i < length l}). mem i (item_index item l 0) = true ==> index l i = item)
  = forall_intro (index_is_mem_is_item_forall_i l)

let index_not_mem_not_item_not_item_not_mem (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a) (i:nat{i < length l}). mem i (item_index item l 0) = false <==> index l i <> item)
  = index_is_not_item_is_not_mem l;
    index_is_not_mem_is_not_item l

let index_mem_item_item_mem (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a) (i:nat{i < length l}). mem i (item_index item l 0) = true <==> index l i = item)
  = index_is_item_is_mem l;
    index_is_mem_is_item l

let rec mem_index_element (#a:eqtype) (l:list a) (i:nat{i < length l})
  : Lemma (ensures mem (index l i) l = true)
  = match l with 
    | [] -> ()
    | hd :: tl -> match i with
                  | 0 -> ()
                  | _ -> mem_index_element tl (i - 1)

let mem_index_element_forall (#a:eqtype) (l:list a)
  : Lemma (ensures forall (i:nat{i < length l}). mem (index l i) l = true)
  = forall_intro (mem_index_element l)

let rec index_not_zero_not_first_element (#a:eqtype) (l:list a) (item:a) (m:nat) (i:nat{i < length (item_index item l m)})
  : Lemma (requires length (item_index item l m) > 1)
          (ensures 
           (let indices = item_index item l m in
            i <> 0 ==> index indices i <> hd indices))
  = match l with 
    | [] -> ()
    | fst :: tl -> if fst = item 
                   then (
                    assert(hd (item_index item l m) = m);
                    assert(item_index item l m = m :: (item_index item tl (m + 1)));
                    match i with 
                    | 0 -> ()
                    | _ -> mem_index_element (item_index item tl (m + 1)) (i - 1);
                           item_indices_is_in_interval item tl (m + 1) (index (item_index item tl (m + 1)) (i - 1))
                   )
                   else index_not_zero_not_first_element tl item (m + 1) i

let rec hd_item_indices_is_min (#a:eqtype) (l:list a) (item:a) (i:nat) (m:nat)
  : Lemma (requires length (item_index item l m) > 1)
          (ensures 
           (let indices = item_index item l m in 
            mem i indices && i <> hd indices ==> i > hd indices))
  = match l with 
    | [] -> ()
    | fst :: tl -> if fst = item 
                   then item_indices_is_in_interval item tl (m + 1) i
                   else hd_item_indices_is_min tl item i (m + 1)

let subtraction (i:nat) : nat
  = if i > 0
    then i - 1
    else i

let proof_subtraction (i:nat)
  : Lemma (ensures i > 0 ==> subtraction i = i - 1)
  = ()

let rec item_indices_zero_is_item_indices_one_minus_one (#a:eqtype) (l:list a) (item:a) (m:nat)
  : Lemma (ensures item_index item l m = map subtraction (item_index item l (m + 1)))
  = match l with 
    | [] -> ()
    | hd :: tl -> item_indices_zero_is_item_indices_one_minus_one tl item (m + 1)

let rec item_map_subtraction (l:list nat) (i:nat{i < length l})
  : Lemma (ensures 
           (let l' = map subtraction l in
            index l i > 0 ==> index l' i = (index l i) - 1))
  = match l with
    | [] -> ()
    | fst :: tl -> match i with 
                  | 0 -> ()
                  | _ -> item_map_subtraction tl (i - 1)

//item_indices item l m
let rec indices_are_ordered_in_ascending_order (#a:eqtype) (l:list a) (item:a) (i:nat) (j:nat)
  : Lemma (requires i < length (item_index item l 0) && j < length (item_index item l 0) && i < j)
          (ensures 
           (let indices = item_index item l 0 in
            index indices i < index indices j))
  = match l with 
    | [] -> ()
    | fst :: tl -> match i with 
                  | 0 -> if fst = item 
                         then (
                          mem_index_element (item_index item tl 1) (j - 1);
                          item_indices_is_in_interval item tl 1 (index (item_index item tl 1) (j - 1))
                         )
                         else (
                          if length (item_index item tl 1) < 2
                          then ()
                          else (
                            mem_index_element (item_index item l 0) j;
                            index_not_zero_not_first_element l item 0 j;
                            hd_item_indices_is_min l item (index (item_index item l 0) j) 0
                          )
                         )
                  | _ -> item_indices_zero_is_item_indices_one_minus_one tl item 0;
                         assert((item_index item tl 0) = map subtraction (item_index item tl 1));
                         if fst = item
                         then (
                          assert(index (item_index item l 0) i = index (item_index item tl 1) (i - 1));
                          assert(index (item_index item l 0) j = index (item_index item tl 1) (j - 1));
                          mem_index_element (item_index item tl 1) (i - 1);
                          mem_index_element (item_index item tl 1) (j - 1);
                          item_map_subtraction (item_index item tl 1) (i - 1);
                          item_map_subtraction (item_index item tl 1) (j - 1);
                          item_indices_is_in_interval item tl 1 (index (item_index item tl 1) (i - 1));
                          item_indices_is_in_interval item tl 1 (index (item_index item tl 1) (j - 1));
                          assert(index (item_index item tl 0) (i - 1) = (index (item_index item tl 1) (i - 1)) - 1);
                          assert(index (item_index item tl 0) (j - 1) = (index (item_index item tl 1) (j - 1)) - 1);
                          indices_are_ordered_in_ascending_order tl item (i - 1) (j - 1)
                         )
                         else (
                          assert(index (item_index item l 0) i = index (item_index item tl 1) i);
                          assert(index (item_index item l 0) j = index (item_index item tl 1) j);
                          mem_index_element (item_index item tl 1) i;
                          mem_index_element (item_index item tl 1) j;
                          item_map_subtraction (item_index item tl 1) i;
                          item_map_subtraction (item_index item tl 1) j;
                          item_indices_is_in_interval item tl 1 (index (item_index item tl 1) i);
                          item_indices_is_in_interval item tl 1 (index (item_index item tl 1) j);
                          assert(index (item_index item tl 0) i = (index (item_index item tl 1) i) - 1);
                          assert(index (item_index item tl 0) j = (index (item_index item tl 1) j) - 1);
                          indices_are_ordered_in_ascending_order tl item i j 
                         )

let rec last_is_length_l_minus_one (#a:eqtype) (l:list a)
  : Lemma (requires l <> [])
          (ensures last l = index l ((length l) - 1))
  = match l with
    | [el] -> ()
    | hd :: tl -> last_is_length_l_minus_one tl

let last_index_is_max_base (#a:eqtype) (item:a) (l:list a{item_index item l 0 <> []}) (i:nat{i < length (item_index item l 0) - 1})
  : Lemma (ensures 
           (let indices = item_index item l 0 in
            let j = (length indices) - 1 in
            index indices i < index indices j))
  = indices_are_ordered_in_ascending_order l item i (length (item_index item l 0) - 1)

let last_index_is_max (#a:eqtype) (item:a) (l:list a{item_index item l 0 <> []}) 
  : Lemma (ensures forall (i:nat{i < length (item_index item l 0) - 1}).
           (let indices = item_index item l 0 in
            let j = (length indices) - 1 in
            index indices i < index indices j))
  = forall_intro (last_index_is_max_base item l)

let new_or_old (#a:eqtype) (c:a) (l:list a) : int
  = if item_index c l 0 <> []
    then last (item_index c l 0)
    else -1

let rec mem_last_list (#a:eqtype) (l:list a)
  : Lemma (requires l <> [])
          (ensures mem (last l) l = true)
  = match l with 
    | [el] -> ()
    | hd :: tl -> mem_last_list tl

let new_or_old_return_values (#a:eqtype) (l:list a) (item:a)
  : Lemma (ensures new_or_old item l = -1 || (new_or_old item l >= 0 && new_or_old item l < length l))
  = if item_index item l 0 = []
    then ()
    else (
      mem_last_list (item_index item l 0);
      item_indices_is_in_interval item l 0 (last (item_index item l 0))
    )

let rec not_new_or_old_empty_list (#a:eqtype) (l:list a) (item:a)
  : Lemma (ensures new_or_old item l = -1 ==> item_index item l 0 = [])
  = match l with
    | [] -> ()
    | hd :: tl -> not_new_or_old_empty_list tl item 

let rec empty_list_length_zero (#a:eqtype) (l:list a) (item:a)
  : Lemma (ensures item_index item l 0 = [] ==> length (item_index item l 0) = 0)
  = match l with 
    | [] -> ()
    | hd :: tl -> empty_list_length_zero tl item

let rec length_zero_count_zero (#a:eqtype) (l:list a) (item:a)
  : Lemma (ensures length (item_index item l 0) = 0 ==> count item l = 0)
  = match l with
    | [] -> ()
    | hd :: tl -> length_zero_count_zero tl item;
                  item_list_has_correct_length l 0

let rec count_zero_mem_false (#a:eqtype) (l:list a) (item:a)
  : Lemma (ensures count item l = 0 ==> mem item l = false)
  = match l with
    | [] -> ()
    | hd :: tl -> count_zero_mem_false tl item
                 
let rec mem_false_not_item (#a:eqtype) (l:list a) (item:a) (i:nat{i < length l})
  : Lemma (ensures mem item l = false ==> index l i <> item)
  = match l with 
    | [] -> ()
    | hd :: tl -> match i with 
                  | 0 -> ()
                  | _ -> mem_false_not_item tl item (i - 1)

let rec new_or_old_not_item_base (#a:eqtype) (l:list a) (item:a) (i:nat{i < length l})
  : Lemma (ensures new_or_old item l = -1 ==> index l i <> item)
  = match l with
    | [] -> ()
    | hd :: tl -> match i with 
                  | 0 -> ()
                  | _ -> new_or_old_not_item_base tl item (i - 1);
                         not_new_or_old_empty_list l item;
                         empty_list_length_zero l item;
                         length_zero_count_zero l item;
                         count_zero_mem_false l item;
                         mem_false_not_item l item i

let new_or_old_not_item (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a) (i:nat{i < length l}). new_or_old item l = -1 ==> index l i <> item)
  = forall_intro_2 (new_or_old_not_item_base l)   

let rec new_or_old_not_empty_list (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a). new_or_old item l <> -1 ==> item_index item l 0 <> [])
  = match l with
    | [] -> ()
    | hd :: tl -> new_or_old_not_empty_list tl

let rec not_empty_list_length_greater_than_zero_base (#a:eqtype) (l:list a) (item:a)
  : Lemma (ensures item_index item l 0 <> [] ==> mem (last (item_index item l 0)) (item_index item l 0) = true)
  = match l with
    | [] -> ()
    | hd :: tl -> not_empty_list_length_greater_than_zero_base tl item;
                  if item_index item l 0 <> []
                  then mem_last_list (item_index item l 0)
                  else ()

let not_empty_list_length_greater_than_zero (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a). item_index item l 0 <> [] ==> mem (last (item_index item l 0)) (item_index item l 0) = true)
  = forall_intro (not_empty_list_length_greater_than_zero_base l)
 
let mem_index_is_item (#a:eqtype) (item:a) (l:list a)
  : Lemma (requires item_index item l 0 <> [] && last (item_index item l 0) < length l)
          (ensures mem (last (item_index item l 0)) (item_index item l 0) = true ==> index l (last (item_index item l 0)) = item)
  = mem_last_list (item_index item l 0);
    index_is_mem_is_item l

let rec index_plus_one_base (#a:eqtype) (l:list a) (item:a) (el:a) (i:nat{i < length l})
  : Lemma (ensures index l i = item ==> index (el :: l) (i + 1) = item)
  = match l with
    | [] -> ()
    | hd :: tl -> match i with 
                  | 0 -> ()
                  | _ -> index_plus_one_base tl item hd (i - 1)

let index_plus_one (#a:eqtype) (l:list a) (item:a) (el:a)
  : Lemma (ensures forall (i:nat{i < length l}). index l i = item ==> index (el :: l) (i + 1) = item)
  = forall_intro (index_plus_one_base l item el)

let rec exists_tl_exists_tl_plus_hd (#a:eqtype) (l:list a) (item:a) (el:a)
  : Lemma (ensures (exists (i:nat{i < length l}). index l i = item) ==> (exists (i:nat{i < length (el :: l)}). index (el :: l) i = item))
  = match l with 
    | [] -> ()
    | hd :: tl -> if hd = item 
                  then (
                    assert(index l 0 = item);
                    assert(index (el :: l) 1 = item)
                  )
                  else exists_tl_exists_tl_plus_hd tl item hd;
                       index_plus_one l item el

let rec mem_list_exists_index (#a:eqtype) (l:list a) (item:a)
  : Lemma (ensures mem item l = true ==> (exists (i:nat{i < length l}). index l i = item))
  = match l with 
    | [] -> ()
    | hd :: tl -> if hd = item 
                  then assert(index l 0 = item)
                  else (
                    mem_list_exists_index tl item;
                    exists_tl_exists_tl_plus_hd tl item hd
                  )

let index_in_list_is_less_than_last_base (#a:eqtype) (item:a) (l:list a{item_index item l 0 <> []}) (x:nat)
  : Lemma (ensures mem x (item_index item l 0) = true ==> x <= last (item_index item l 0))
  = mem_list_exists_index (item_index item l 0) x;
    last_index_is_max item l;
    last_is_length_l_minus_one (item_index item l 0)

let index_in_list_is_less_than_last (#a:eqtype) (item:a) (l:list a{item_index item l 0 <> []})
  : Lemma (ensures forall (i:nat). mem i (item_index item l 0) = true ==> i <= last (item_index item l 0))
  = forall_intro (index_in_list_is_less_than_last_base item l)

let index_greater_than_last_not_item (#a:eqtype) (item:a) (l:list a{item_index item l 0 <> []}) (i:nat{i < length l})
  : Lemma (ensures i > (last (item_index item l 0)) ==> index l i <> item)
  = index_is_not_mem_is_not_item_forall_i l item;
    index_in_list_is_less_than_last item l

let mem_index_is_item_last_indices_are_not_item_base (#a:eqtype) (item:a) (l:list a{item_index item l 0 <> []}) (i:nat{i > (last (item_index item l 0)) && i < length l})
  : Lemma (ensures mem (last (item_index item l 0)) (item_index item l 0) = true ==> index l i <> item)
  = index_greater_than_last_not_item item l i

let mem_index_is_item_last_indices_are_not_item (#a:eqtype) (item:a) (l:list a{item_index item l 0 <> []})
  : Lemma (ensures mem (last (item_index item l 0)) (item_index item l 0) = true ==> (forall (i:nat{i > (last (item_index item l 0)) && i < length l}). index l i <> item))
  = forall_intro (index_greater_than_last_not_item item l)

let mem_index_is_item_gives_correct_result (#a:eqtype) (l:list a) (item:a)
  : Lemma (requires item_index item l 0 <> [] && (last (item_index item l 0)) < length l)
          (ensures mem (last (item_index item l 0)) (item_index item l 0) = true ==> index l (last (item_index item l 0)) = item /\ 
          (forall (i:nat{i > (last (item_index item l 0)) && i < length l}). index l i <> item))
  = mem_index_is_item item l;
    mem_index_is_item_last_indices_are_not_item item l

let new_or_old_not_empty_list_correct_item_base (#a:eqtype) (l:list a) (item:a)
  : Lemma (requires item_index item l 0 <> [] && last (item_index item l 0) < length l)
          (ensures new_or_old item l <> -1 ==> index l (last (item_index item l 0)) = item /\ 
          (forall (i:nat{i > (last (item_index item l 0)) && i < length l}). index l i <> item))
  = new_or_old_not_empty_list l;
    not_empty_list_length_greater_than_zero l;
    mem_index_is_item_gives_correct_result l item

let new_or_old_not_empty_list_correct_item_implication (#a:eqtype) (l:list a) (item:a)
  : Lemma (ensures (item_index item l 0 <> [] && last (item_index item l 0) < length l) ==> 
                   (new_or_old item l <> -1 ==> index l (last (item_index item l 0)) = item /\
                   (forall (i:nat{i > (last (item_index item l 0)) && i < length l}). index l i <> item)))
  = if item_index item l 0 = []
    then ()
    else (
      mem_last_list (item_index item l 0);
      item_indices_is_in_interval_forall item l 0;
      assert(item_index item l 0 <> [] && last (item_index item l 0) < length l);
      // move_requires (new_or_old_not_empty_list_correct_item_base l) item
      admit()
    )
    
val update_bc (a:list english_letters) (p:list english_letters) : list int
let rec update_bc a p = 
    match a with 
    | [] -> []
    | hd :: tl -> (new_or_old hd p) :: update_bc tl p

let rec update_bc_length_is_initial_list_length (l:list english_letters) (p:list english_letters)
  : Lemma (ensures length (update_bc l p) = length l)
  = match l with 
    | [] -> ()
    | hd :: tl -> update_bc_length_is_initial_list_length tl p

let rec update_bc_has_index_minusone_if_letter_is_not_in_pattern_base (l:list english_letters) (p:list english_letters)
                                                                      (i:nat{i < length l && i < length (update_bc l p)}) (j:nat{j < length p})
  : Lemma (ensures 
           (let l' = update_bc l p in
            index l' i = -1 ==> index p j <> index l i))
  = update_bc_length_is_initial_list_length l p;
    match l with 
    | [] -> ()
    | fst :: tl -> match i with 
                   | 0 -> assert(update_bc l p = (new_or_old fst p) :: update_bc tl p);
                          assert(index (update_bc l p) i = new_or_old fst p);
                          assert(fst = index l i);
                          new_or_old_not_item_base p fst j;
                          assert(new_or_old fst p = - 1 ==> index p j <> fst)
                   | _ -> update_bc_has_index_minusone_if_letter_is_not_in_pattern_base tl p (i - 1) j

let update_bc_has_index_minusone_if_letter_is_not_in_pattern_forall_j (l:list english_letters) 
                                                                      (p:list english_letters) 
                                                                      (i:nat{i < length l && i < length (update_bc l p)})
  : Lemma (ensures forall (j:nat{j < length p}).  
           (let l' = update_bc l p in
            index l' i = -1 ==> index p j <> index l i))
  = forall_intro (update_bc_has_index_minusone_if_letter_is_not_in_pattern_base l p i)

let update_bc_has_index_minusone_if_letter_is_not_in_pattern (l:list english_letters) (p:list english_letters)
  : Lemma (ensures forall (i:nat{i < length l && i < length (update_bc l p)}). (forall (j:nat{j < length p}).  
           (let l' = update_bc l p in
            index l' i = -1 ==> index p j <> index l i)))
  = forall_intro (update_bc_has_index_minusone_if_letter_is_not_in_pattern_forall_j l p)

let rec update_bc_has_correct_index_if_letter_is_in_pattern_base (l:list english_letters)
                                                                 (p:list english_letters)
                                                                 (i:nat{i < length l && i < length (update_bc l p)}) 
                                                                 (j:nat{j < length p})
  : Lemma (ensures 
           (let l' = update_bc l p in
            index l' i = j ==> index p j = index l i /\ (forall (i':nat{i' > j && i' < length p}). index p i' <> index l i)))
  = update_bc_length_is_initial_list_length l p;
    match l with 
    | [] -> ()
    | fst :: tl -> match i with 
                   | 0 -> assert(update_bc l p = (new_or_old fst p) :: update_bc tl p);
                          assert(index (update_bc l p) i = new_or_old fst p);
                          assert(fst = index l i);
                          if j = new_or_old fst p
                          then (
                            if item_index (index l i) l 0 <> []
                            then (
                              item_indices_is_in_interval (index l i) l 0 (last (item_index (index l i) l 0));
                              new_or_old_not_empty_list_correct_item_base p fst
                            )
                            else ()
                          )
                          else ()
                   | _ -> update_bc_has_correct_index_if_letter_is_in_pattern_base tl p (i - 1) j

let update_bc_has_correct_index_if_letter_is_in_pattern_forall_j (l:list english_letters) 
                                                                 (p:list english_letters)
                                                                 (i:nat{i < length l && i < length (update_bc l p)})
  : Lemma (ensures 
           (let l' = update_bc l p in forall (j:nat{j < length p}).
            index l' i = j ==> index p j = index l i /\ (forall (i':nat{i' > j && i' < length p}). index p i' <> index l i)))
  = forall_intro (update_bc_has_correct_index_if_letter_is_in_pattern_base l p i)

let update_bc_has_correct_index_if_letter_is_in_pattern (l:list english_letters) (p:list english_letters)
  : Lemma (ensures 
           (let l' = update_bc l p in forall (i:nat{i < length l && i < length (update_bc l p)}) (j:nat{j < length p}).
            index l' i = j ==> index p j = index l i /\ 
            (forall (i':nat{i' > j && i' < length p}). index p i' <> index l i)))
  = forall_intro (update_bc_has_correct_index_if_letter_is_in_pattern_forall_j l p)

let rec update_bc_has_values_in_interval (l:list english_letters) (p:list english_letters) (i:nat{i < length (update_bc l p)})
  : Lemma (ensures 
           (let l' = update_bc l p in 
            index l' i = -1 || (index l' i >= 0 && index l' i < length p)))
  = match l with 
    | [] -> ()
    | fst :: tl -> if i = 0 
                   then new_or_old_return_values p fst
                   else update_bc_has_values_in_interval tl p  (i - 1)

let final_bc : list int = update_bc alphabet pattern

let update_bc_has_index_minusone_if_letter_is_not_in_pattern_for_alphabet ()
  : Lemma (ensures forall (i:nat{i < length alphabet && i < length (update_bc alphabet pattern)}). (forall (j:nat{j < length pattern}).  
           (let l' = update_bc alphabet pattern in
            index l' i = -1 ==> index pattern j <> index alphabet i)))
  = update_bc_has_index_minusone_if_letter_is_not_in_pattern alphabet pattern

let update_bc_has_correct_index_if_letter_is_in_pattern_for_alphabet ()
  : Lemma (ensures 
           (let l' = update_bc alphabet pattern in forall 
            (i:nat{i < length alphabet && i < length (update_bc alphabet pattern)}) (j:nat{j < length pattern}).
            index l' i = j ==> index pattern j = index alphabet i /\ 
            (forall (i':nat{i' > j && i' < length pattern}). index pattern i' <> index alphabet i)))
  = update_bc_has_correct_index_if_letter_is_in_pattern alphabet pattern

let final_bc_has_same_length_as_alphabet () 
  : Lemma (ensures length final_bc = length alphabet)
  = update_bc_length_is_initial_list_length alphabet pattern

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

let item_index_of_t_in_alphabet (t:list english_letters) (i:nat{i < length t})
  : Lemma (ensures item_index (index t i) alphabet 0 <> [])
  = match index t i with 
    | A -> assert(index t i = index alphabet 0)
    | B -> assert(index t i = index alphabet 1)

let last_is_less_than_bc (t:list english_letters) (p:list english_letters{length p <= length t}) (i:nat{i < length t}) 
  : Lemma (requires item_index (index t i) alphabet 0 <> [])
          (ensures last (item_index (index t i) alphabet 0) < length (update_bc alphabet p))
  = mem_last_list (item_index (index t i) alphabet 0);
    update_bc_length_is_initial_list_length alphabet p;
    item_indices_is_in_interval (index t i) alphabet 0 (last (item_index (index t i) alphabet 0))

val boyer_moore (t:list english_letters) (p:list english_letters{length p <= length t}) (k:nat{k <= length p}) (i:nat) 
    : Tot (result:int{result >= -1}) 
    (decreases %[(if i < length t - length p + 1 then length t - length p + 1 - i else 0); length p - k])
let rec boyer_moore t p k i =
    let m = length p in
    let n = length t in
    if k = m then i
    else if i > n - m then -1 
    else (
      if index t (i + m - 1 - k) = index p (m - 1 - k)
      then boyer_moore t p (k + 1) i
      else (
        item_index_of_t_in_alphabet t (i + m - 1 - k);
        last_is_less_than_bc t p (i + m - 1 - k);
        let shiftbc = m - k - 1 - index (update_bc alphabet p) (last (item_index (index t (i + m - 1 - k)) alphabet 0)) in
        let value = i + (maximum 1 shiftbc) in
        boyer_moore t p 0 value
      ) 
    )

//don't know if usefull 
let rec length_init_list_is_length_list_minus_one (l:list english_letters)
  : Lemma (requires l <> [])
          (ensures length (init l) = length l - 1)
  = match l with 
    | [el] -> ()
    | hd :: tl -> length_init_list_is_length_list_minus_one tl

//don't know if usefull
let rec p_less_than_t_then_init_p_less_than_t (t:list english_letters) (p:list english_letters{length p <= length t})
  : Lemma (requires length p > 0)
          (ensures length p <= length t ==> length (init p) <= length t)
  = match p with 
    | [el] -> ()
    | hd :: tl -> length_init_list_is_length_list_minus_one p;
                  p_less_than_t_then_init_p_less_than_t t tl

let boyer_moore_result_base (t:list english_letters) (p:list english_letters{length p <= length t}) 
                            (k:nat{k < length p}) (i:nat{i <= length t - length p})
  : Lemma (requires boyer_moore t p k i = boyer_moore t p (length p) i)
          (ensures boyer_moore t p k i = i)
  = ()

let boyer_moore_result_implication (t:list english_letters) (p:list english_letters{length p <= length t}) 
                                   (k:nat{k < length p}) (i:nat{i <= length t - length p})
  : Lemma (ensures boyer_moore t p k i = boyer_moore t p (length p) i ==> boyer_moore t p k i = i)
  = move_requires (boyer_moore_result_base t p k) i

let boyer_moore_result (t:list english_letters) (p:list english_letters{length p <= length t})
  : Lemma (ensures forall (k:nat{k < length p}) (i:nat{i <= length t - length p}). boyer_moore t p k i = boyer_moore t p (length p) i ==> boyer_moore t p k i = i)
  = forall_intro_2 (boyer_moore_result_implication t p)

let rec boyer_moore_value_comparison (t:list english_letters) (p:list english_letters{length p <= length t}) 
                                     (k:nat{k <= length p}) (i:nat)
  : Lemma (ensures boyer_moore t p k i <> boyer_moore t p (length p) i ==> boyer_moore t p k i > i || boyer_moore t p k i = -1)
          (decreases %[(if i < length t - length p + 1 then length t - length p + 1 - i else 0); length p - k])
  = let m = length p in 
    let n = length t in 
    if i > n - m 
    then ()
    else (
      if k = length p
      then ()
      else (
        if index t (i + m - 1 - k) = index p (m - 1 - k) 
        then boyer_moore_value_comparison t p (k + 1) i
        else (
          item_index_of_t_in_alphabet t (i + m - 1 - k);
          last_is_less_than_bc t p (i + m - 1 - k);
          let shiftbc = m - k - 1 - index (update_bc alphabet p) (last (item_index (index t (i + m - 1 - k)) alphabet 0)) in
          let value = i + (maximum 1 shiftbc) in
          boyer_moore_value_comparison t p 0 value
        )
      )
    )

let k_to_m_then_index_is_equal (t:list english_letters) (p:list english_letters{length p <= length t}) 
                                   (k:nat{k < length p}) (i:nat{i <= length t - length p})
  : Lemma (requires boyer_moore t p k i = boyer_moore t p (length p) i)
          (ensures index t (i + length p - 1 - k) = index p (length p - 1 - k))
  = item_index_of_t_in_alphabet t (i + length p - 1 - k);
    last_is_less_than_bc t p (i + length p - 1 - k);
    let bc = update_bc alphabet p in
    let shiftbc = length p - k - 1 - index bc (last (item_index (index t (i + length p - 1 - k)) alphabet 0)) in
    let value = i + (maximum 1 shiftbc) in
    if index t (i + length p - 1 - k) <> index p (length p - 1 - k)
    then (
      assert(index t (i + length p - 1 - k) <> index p (length p - 1 - k) ==> boyer_moore t p k i = boyer_moore t p 0 value);
      boyer_moore_value_comparison t p 0 value;
      assert(boyer_moore t p 0 value > i || boyer_moore t p 0 value = -1);
      assert(boyer_moore t p 0 value <> boyer_moore t p (length p) i)
    )
    else ()

let rec k_to_m_then_k'_index_is_equal_base (t:list english_letters) (p:list english_letters{length p <= length t}) 
                                      (k:nat{k < length p}) (i:nat{i <= length t - length p})
                                      (k':nat{k' >= k && k' < length p})
  : Lemma (requires boyer_moore t p k i = boyer_moore t p (length p) i)
          (ensures index t (i + length p - 1 - k') = index p (length p - 1 - k'))
          (decreases length p - k)
  = k_to_m_then_index_is_equal t p k i;
    if k = length p - 1
    then ()
    else if k = k' then ()
    else (
      assert(index t (i + length p - 1 - k) = index p (length p - 1 - k) ==> boyer_moore t p k i = boyer_moore t p (k + 1) i);
      k_to_m_then_k'_index_is_equal_base t p (k + 1) i k'
    )

let k_to_m_then_k'_index_is_equal_implication (t:list english_letters) (p:list english_letters{length p <= length t}) 
                                              (k:nat{k < length p}) (i:nat{i <= length t - length p})
                                              (k':nat{k' >= k && k' < length p})
  : Lemma (ensures boyer_moore t p k i = boyer_moore t p (length p) i ==> index t (i + length p - 1 - k') = index p (length p - 1 - k'))
  = move_requires (k_to_m_then_k'_index_is_equal_base t p k i) k'

let k_to_m_then_k'_index_is_equal_forall_k' (t:list english_letters) (p:list english_letters{length p <= length t}) 
                                            (k:nat{k < length p}) (i:nat{i <= length t - length p})
  : Lemma (ensures boyer_moore t p k i = boyer_moore t p (length p) i ==> 
           (forall (k':nat{k' >= k && k' < length p}). index t (i + length p - 1 - k') = index p (length p - 1 - k')))
  = forall_intro (k_to_m_then_k'_index_is_equal_implication t p k i)

let k_to_m_then_k'_index_is_equal (t:list english_letters) (p:list english_letters{length p <= length t}) 
  : Lemma (ensures forall (k:nat{k < length p}) (i:nat{i <= length t - length p}). 
           boyer_moore t p k i = boyer_moore t p (length p) i ==> 
           (forall (k':nat{k' >= k && k' < length p}). index t (i + length p - 1 - k') = index p (length p - 1 - k')))
  = forall_intro_3 (k_to_m_then_k'_index_is_equal_implication t p)

let convert_from_x_to_j_base (p:list english_letters) (i:nat) (j:nat{j >= i && j < i + length p})
  : Lemma (ensures exists (x:nat{x < length p}). j = i + length p - 1 - x)
  = let value = i + length p - 1 - j in 
    assert(j >= i && j < i + length p);
    assert(-j > - i - length p && -j <= -i);
    assert(- 1 - j > - i - length p - 1 && - 1 - j <= - i - 1);
    assert(length p - 1 - j > - i - 1 && length p - 1 - j <= length p - i - 1);
    assert(i + length p - 1 - j > -1 && i + length p - 1 - j <= length p - 1);
    assert(value > -1 && value <= length p - 1);
    assert(value >= 0 && value < length p);
    assert(j = i + length p - 1 - value);
    assert(exists (x:nat{x < length p}). j = i + length p - 1 - x)

let convert_from_x_to_j (p:list english_letters) (i:nat)
  : Lemma (ensures forall (j:nat{j >= i && j < i + length p}). exists (x:nat{x < length p}). j = i + length p - 1 - x)
  = forall_intro (convert_from_x_to_j_base p i)

let zero_to_m_then_belongs_true (t:list english_letters) (p:list english_letters{length p <= length t}) 
                                (i:nat{i <= length t - length p})
  : Lemma (requires boyer_moore t p 0 i = boyer_moore t p (length p) i)
          (ensures belongs t p i = true)
  = if length p > 0 
    then (
      k_to_m_then_k'_index_is_equal_forall_k' t p 0 i;
      assert(forall (x:nat{x >= 0 && x < length p}). index t (i + length p - 1 - x) = index p (length p - 1 - x));
      indices_are_equal_belongs_true_base t p i;
      convert_from_x_to_j p i;
      assert(forall (j:nat{j >= i && j < i + length p}). exists (x:nat{x >= 0 && x < length p}). j = i + length p - 1 - x);
      assert(forall (j:nat{j >= i && j < i + length p}). index t j = index p (j - i))
    )
    else ()

let zero_to_k_than_all_indices_are_equal (t:list english_letters) (p:list english_letters{length p <= length t}) 
                                         (k:nat{k < length p}) (i:nat{i <= length t - length p})
  : Lemma (requires //boyer_moore t p 0 i = boyer_moore t p k i /\
                    (forall (k':nat{k' < k}). index t (i + length p - 1 - k') = index p (length p - 1 - k')) /\
                    index t (i + length p - 1 - k) = index p (length p - 1 - k))
          (ensures boyer_moore t p k i = boyer_moore t p (k + 1) i /\
                   (forall (k':nat{k' < k + 1}). index t (i + length p - 1 - k') = index p (length p - 1 - k')))
  = ()

let rec boyer_moore_not_equal_indices_then_increase_i (t:list english_letters) (p:list english_letters{length p <= length t}) 
                                                      (k:nat{k < length p}) (i:nat{i <= length t - length p})
  : Lemma (requires boyer_moore t p k i <> boyer_moore t p (length p) i)
          (ensures exists (k':nat{k' >= k && k' < length p}). index t (i + length p - 1 - k') <> index p (length p - 1 - k'))
          (decreases length p - k)
  = if index t (i + length p - 1 - k) = index p (length p - 1 - k)
    then boyer_moore_not_equal_indices_then_increase_i t p (k + 1) i 
    else ()

let from_zero_to_i_boyer_moore_does_not_return_i_base (t:list english_letters) (p:list english_letters{length p <= length t}) 
                                                      (i:nat{i <= length t - length p}) (i':nat{i' < i})
  : Lemma (requires boyer_moore t p 0 0 = boyer_moore t p 0 i)
          (ensures boyer_moore t p 0 i' <> boyer_moore t p (length p) i')
  = admit()

let from_zero_to_i_boyer_moore_does_not_return_i_implication (t:list english_letters) (p:list english_letters{length p <= length t}) 
                                                             (i:nat{i <= length t - length p}) (i':nat{i' < i})
  : Lemma (ensures boyer_moore t p 0 0 = boyer_moore t p 0 i ==> boyer_moore t p 0 i' <> boyer_moore t p (length p) i')
  = move_requires (from_zero_to_i_boyer_moore_does_not_return_i_base t p i) i'

let from_zero_to_i_boyer_moore_does_not_return_i (t:list english_letters) (p:list english_letters{length p <= length t}) 
                                                 (i:nat{i <= length t - length p}) 
  : Lemma (ensures forall (i':nat{i' < i}). boyer_moore t p 0 0 = boyer_moore t p 0 i ==> boyer_moore t p 0 i' <> boyer_moore t p (length p) i')
  = forall_intro (from_zero_to_i_boyer_moore_does_not_return_i_implication t p i)

let from_zero_to_i_belongs_is_false (t:list english_letters) (p:list english_letters{length p <= length t}) 
                                    (i:nat{i <= length t - length p}) (i':nat{i' < i})
  : Lemma (requires boyer_moore t p 0 0 = boyer_moore t p 0 i)
          (ensures belongs t p i' = false)
  = from_zero_to_i_boyer_moore_does_not_return_i t p i;
    boyer_moore_not_equal_indices_then_increase_i t p 0 i';
    index_is_not_equal_belongs_false_base t p i'

let boyer_moore_to_value_then_not_boyer_moore_to_length_p (t:list english_letters) (p:list english_letters{length p <= length t}) 
                                                          (k:nat{k < length p}) (i:nat{i <= length t - length p}) 
  : Lemma (requires item_index (index t (i + length p - 1 - k)) alphabet 0 <> [] /\
           last (item_index (index t (i + length p - 1 - k)) alphabet 0) < length (update_bc alphabet p) /\
          (let bc = update_bc alphabet p in
           let shiftbc = length p - k - 1 - index bc (last (item_index (index t (i + length p - 1 - k)) alphabet 0)) in
           let value = i + (maximum 1 shiftbc) in
          //  boyer_moore t p 0 i = boyer_moore t p k i /\
           (forall (k':nat{k' < k}). index t (i + length p - 1 - k') = index p (length p - 1 - k')) /\
           index t (i + length p - 1 - k) <> index p (length p - 1 - k)))
          (ensures boyer_moore t p k i <> boyer_moore t p (length p) i)
  = assert(boyer_moore t p (length p) i = i);
    let bc = update_bc alphabet p in
    let shiftbc = length p - k - 1 - index bc (last (item_index (index t (i + length p - 1 - k)) alphabet 0)) in
    let value = i + (maximum 1 shiftbc) in
    update_bc_length_is_initial_list_length alphabet p;
    assert(length bc = length alphabet);
    boyer_moore_value_comparison t p 0 value

let number_is_in_interval (i:nat) (i':nat{i' >= i && i' < i + 1})
  : Lemma (ensures i' = i)
  = ()

let boyer_moore_belongs_false_if_less_than_shiftbc (t:list english_letters) (p:list english_letters{length p <= length t}) 
                                                   (k:nat{k < length p}) (i:nat{i <= length t - length p}) 
                                                   (i':nat{i' >= i})
  : Lemma (requires item_index (index t (i + length p - 1 - k)) alphabet 0 <> [] /\
           last (item_index (index t (i + length p - 1 - k)) alphabet 0) < length (update_bc alphabet p) /\
          (let bc = update_bc alphabet p in
           let shiftbc = length p - k - 1 - index bc (last (item_index (index t (i + length p - 1 - k)) alphabet 0)) in
           let value = i + (maximum 1 shiftbc) in
           //boyer_moore t p 0 0 = boyer_moore t p 0 i /\ 
           //boyer_moore t p 0 i = boyer_moore t p k i /\
           (forall (j:nat{j < i}). belongs t p j = false) /\
           (forall (k':nat{k' < k}). index t (i + length p - 1 - k') = index p (length p - 1 - k')) /\
           index t (i + length p - 1 - k) <> index p (length p - 1 - k) /\ i' < minimum value (length t - length p + 1)))
          (ensures belongs t p i' = false)
          (decreases length p - k)
  = let bc = update_bc alphabet p in
    let shiftbc = length p - k - 1 - index bc (last (item_index (index t (i + length p - 1 - k)) alphabet 0)) in
    let value = i + (maximum 1 shiftbc) in
    // assert(boyer_moore t p 0 0 = boyer_moore t p 0 i);
    // assert(boyer_moore t p 0 i = boyer_moore t p k i);
    assert(forall (k':nat{k' < k}). index t (i + length p - 1 - k') = index p (length p - 1 - k'));
    assert(index t (i + length p - 1 - k) <> index p (length p - 1 - k));
    item_index_of_t_in_alphabet t (i + length p - 1 - k);
    last_is_less_than_bc t p (i + length p - 1 - k);
    boyer_moore_to_value_then_not_boyer_moore_to_length_p t p k i;
    assert(boyer_moore t p k i <> boyer_moore t p (length p) i);
    //assert(boyer_moore t p k i = boyer_moore t p 0 value);
    if shiftbc > 0
    then (
      assert(index bc (last (item_index (index t (i + length p - 1 - k)) alphabet 0)) < length p - 1 - k);
      assert(i + length p - 1 - k >= 0 && i + length p - 1 - k < length t);
      update_bc_length_is_initial_list_length alphabet p;
      update_bc_has_values_in_interval alphabet p (last (item_index (index t (i + length p - 1 - k)) alphabet 0));
      assert(index bc (last (item_index (index t (i + length p - 1 - k)) alphabet 0)) = -1 || 
            (index bc (last (item_index (index t (i + length p - 1 - k)) alphabet 0)) >= 0 &&
              index bc (last (item_index (index t (i + length p - 1 - k)) alphabet 0)) < length p));

      let a = last (item_index (index t (i + length p - 1 - k)) alphabet 0) in 
      let b = index bc (last (item_index (index t (i + length p - 1 - k)) alphabet 0)) in
        
      if b = -1 
      then (
        update_bc_has_index_minusone_if_letter_is_not_in_pattern_forall_j alphabet p a;
        assert(forall (j:nat{j < length p}). index p j <> index alphabet a);

        mem_last_list (item_index (index t (i + length p - 1 - k)) alphabet 0);
        assert(mem a (item_index (index t (i + length p - 1 - k)) alphabet 0) = true);
          
        index_is_mem_is_item_base alphabet (index t (i + length p - 1 - k)) a;
        assert(index alphabet a = index t (i + length p - 1 - k));
        assert(forall (z:nat{z < length p}). index p z <> index t (i + length p - 1 - k))
      )
      else (
        update_bc_has_correct_index_if_letter_is_in_pattern_base alphabet p a b;
        assert(index bc a = b);
        assert(index p b = index alphabet a);
        assert(forall (c:nat{c > b && c < length p}). index p c <> index alphabet a);

        mem_last_list (item_index (index t (i + length p - 1 - k)) alphabet 0);
        assert(mem a (item_index (index t (i + length p - 1 - k)) alphabet 0) = true);
          
        index_is_mem_is_item_base alphabet (index t (i + length p - 1 - k)) a;
        assert(index alphabet a = index t (i + length p - 1 - k));
        // assert(index p b = index t (i + length p - 1 - k));
        assert(forall (d:nat{d > b && d < length p}). index p d <> index t (i + length p - 1 - k));

        assert(shiftbc = maximum 1 shiftbc);
        assert(index t (i + length p - 1 - k) <> index p (length p - 1 - k));
          
        // assert(b = index bc (last (item_index (index t (i + length p - 1 - k)) alphabet 0)));
        // assert(b = length p - 1 - k - shiftbc);
        // assert(index p (length p - 1 - k - shiftbc) = index t (i + length p - 1 - k));
        assert(value = i + shiftbc);
        assert(i' >= i && i' < i + shiftbc);
        assert(i' - i >= 0 && i' - i < shiftbc);
        assert(forall (e:nat{e > length p - 1 - k - shiftbc && e < length p}). index p e <> index t (i + length p - 1 - k));
          
        assert(length p - 1 - k - shiftbc >= 0 && length p - 1 - k - shiftbc < length p);
        assert(length p - 1 - k - (i' - i) > length p - 1 - k - shiftbc);
        assert(i' - i >= 0);
        assert(index p (length p - 1 - k - (i' - i)) <> index t (i + length p - 1 - k));
        assert(index p (i + length p - 1 - k - i') <> index t (i + length p - 1 - k))
      )
    )
    else (
      assert(1 = maximum 1 shiftbc);
      assert(value = i + 1);
      assert(i <= length t - length p);
      assert(value <= length t - length p + 1);
      assert(minimum value (length t - length p + 1) = value);
      assert(minimum value (length t - length p + 1) = i + 1);
      assert(i' >= i && i' < i + 1);
      assert(i' = i);
      assert(index t (i + length p - 1 - k) <> index p (length p - 1 - k))
    );
    index_is_not_equal_belongs_false_base t p i';
    assert((exists (y:nat{y >= i' && y < i' + length p}). index t y <> index p (y - i')) ==> belongs t p i' = false);
    assert(i + length p - 1 - k >= i')
    // assert(i + length p - 1 - k < i' + length p)

let boyer_moore_belongs_false_if_less_than_shiftbc_implication (t:list english_letters) (p:list english_letters{length p <= length t}) 
                                                               (k:nat{k < length p}) (i:nat{i <= length t - length p}) 
                                                               (i':nat{i' >= i})
  : Lemma (ensures (item_index (index t (i + length p - 1 - k)) alphabet 0 <> [] /\
           last (item_index (index t (i + length p - 1 - k)) alphabet 0) < length (update_bc alphabet p) /\
          (let bc = update_bc alphabet p in
           let shiftbc = length p - k - 1 - index bc (last (item_index (index t (i + length p - 1 - k)) alphabet 0)) in
           let value = i + (maximum 1 shiftbc) in
          //  boyer_moore t p 0 0 = boyer_moore t p 0 i /\ 
          //  boyer_moore t p 0 i = boyer_moore t p k i /\
           (forall (j:nat{j < i}). belongs t p j = false) /\
           (forall (k':nat{k' < k}). index t (i + length p - 1 - k') = index p (length p - 1 - k')) /\
           index t (i + length p - 1 - k) <> index p (length p - 1 - k) /\ i' < minimum value (length t - length p + 1)))
           ==> belongs t p i' = false)
  = move_requires (boyer_moore_belongs_false_if_less_than_shiftbc t p k i) i'

let boyer_moore_belongs_false_if_less_than_shiftbc_forall (t:list english_letters) (p:list english_letters{length p <= length t}) 
                                                          (k:nat{k < length p}) (i:nat{i <= length t - length p}) 
  : Lemma (ensures forall (i':nat{i' >= i}). (item_index (index t (i + length p - 1 - k)) alphabet 0 <> [] /\
           last (item_index (index t (i + length p - 1 - k)) alphabet 0) < length (update_bc alphabet p) /\
          (let bc = update_bc alphabet p in
           let shiftbc = length p - k - 1 - index bc (last (item_index (index t (i + length p - 1 - k)) alphabet 0)) in
           let value = i + (maximum 1 shiftbc) in
          //  boyer_moore t p 0 0 = boyer_moore t p 0 i /\ 
          //  boyer_moore t p 0 i = boyer_moore t p k i /\
           (forall (j:nat{j < i}). belongs t p j = false) /\
           (forall (k':nat{k' < k}). index t (i + length p - 1 - k') = index p (length p - 1 - k')) /\
           index t (i + length p - 1 - k) <> index p (length p - 1 - k) /\ i' < minimum value (length t - length p + 1)))
           ==> belongs t p i' = false)
  = forall_intro (boyer_moore_belongs_false_if_less_than_shiftbc_implication t p k i)

let forall_true_and_for_k_true_then_forall_plus_one_true (t:list english_letters) (p:list english_letters{length p <= length t})
                                                         (k:nat{k < length p}) (i:nat{i <= length t - length p})
  : Lemma (requires (forall (k':nat{k' < k}). index t (i + length p - 1 - k') = index p (length p - 1 - k')) /\
                     index t (i + length p - 1 - k) = index p (length p - 1 - k))
          (ensures forall (k':nat{k' < k + 1}). index t (i + length p - 1 - k') = index p (length p - 1 - k'))
  = ()

let rec boyer_moore_gives_correct_result (t:list english_letters) (p:list english_letters{length p <= length t})
                                         (k:nat{k <= length p}) (i:nat{i <= length t - length p})
  : Lemma (requires //boyer_moore t p 0 0 = boyer_moore t p 0 i /\ 
           (forall (i':nat{i' < i}). belongs t p i' = false) /\ 
          //  boyer_moore t p 0 i = boyer_moore t p k i /\
           (forall (k':nat{k' < k}). index t (i + length p - 1 - k') = index p (length p - 1 - k')))
          (ensures 
          (let x = boyer_moore t p k i in 
           x <> -1 ==> belongs t p x = true))
          (decreases %[(if i < length t - length p + 1 then length t - length p + 1 - i else 0); length p - k])
  = if k = length p
    then (
      assert(forall (k':nat{k' < length p}). index t (i + length p - 1 - k') = index p (length p - 1 - k'));
      indices_are_equal_belongs_true_base t p i;
      convert_from_x_to_j p i
    )
    else (
      if index t (i + length p - 1 - k) = index p (length p - 1 - k)
      then (
        zero_to_k_than_all_indices_are_equal t p k i;
        boyer_moore_gives_correct_result t p (k + 1) i 
      )
      else (
        item_index_of_t_in_alphabet t (i + length p - 1 - k);
        last_is_less_than_bc t p (i + length p - 1 - k);
        let shiftbc = length p - k - 1 - index (update_bc alphabet p) (last (item_index (index t (i + length p - 1 - k)) alphabet 0)) in
        let value = i + (maximum 1 shiftbc) in
        if value > length t - length p
        then ()
        else (
          boyer_moore_belongs_false_if_less_than_shiftbc_forall t p k i;
          boyer_moore_gives_correct_result t p 0 value
        )
      )
    )

let boyer_moore_gives_correct_result_for_text_and_pattern ()
  : Lemma (ensures 
          (let x = boyer_moore text pattern 0 0 in 
           x <> -1 ==> belongs text pattern x = true))
  = assert(0 <= length text - length pattern);
    boyer_moore_gives_correct_result text pattern 0 0

//for requires 
let rec boyer_moore_gives_minus_one_belongs_false (t:list english_letters) (p:list english_letters{length p <= length t})
                                                  (k:nat{k <= length p}) (i:nat{i <= length t - length p})
  : Lemma (requires //boyer_moore t p 0 0 = boyer_moore t p 0 i /\ 
           (forall (i':nat{i' < i}). belongs t p i' = false) /\ 
          //  boyer_moore t p 0 i = boyer_moore t p k i /\
           (forall (k':nat{k' < k}). index t (i + length p - 1 - k') = index p (length p - 1 - k')))
          (ensures 
          (let x = boyer_moore t p k i in 
           x = -1 ==> (forall (y:nat{y <= length t - length p}). belongs t p y = false)))
          (decreases %[(if i < length t - length p + 1 then length t - length p + 1 - i else 0); length p - k])
  = if k = length p 
    then ()
    else (
      assert(k < length p);
      if index t (i + length p - 1 - k) = index p (length p - 1 - k)
      then (
        zero_to_k_than_all_indices_are_equal t p k i;
        boyer_moore_gives_minus_one_belongs_false t p (k + 1) i
      )
      else (
        item_index_of_t_in_alphabet t (i + length p - 1 - k);
        last_is_less_than_bc t p (i + length p - 1 - k);
        let shiftbc = length p - k - 1 - index (update_bc alphabet p) (last (item_index (index t (i + length p - 1 - k)) alphabet 0)) in
        let value = i + (maximum 1 shiftbc) in
        boyer_moore_belongs_false_if_less_than_shiftbc_forall t p k i; 
        if value > length t - length p 
        then ()
        else boyer_moore_gives_minus_one_belongs_false t p 0 value
      )
    )

let boyer_moore_gives_minus_one_belongs_false_for_text_and_pattern ()
  : Lemma (ensures 
          (let x = boyer_moore text pattern 0 0 in 
           x = -1 ==> (forall (y:nat{y <= length text - length pattern}). belongs text pattern y = false)))
  = boyer_moore_gives_minus_one_belongs_false text pattern 0 0

let string_of_int_list l =
Printf.sprintf "[%s]"
(String.concat "; " (List.Tot.map (Printf.sprintf "%d") l))

let main() =
  let message =
     if length pattern <= length text
     then sprintf "The result is %d." (boyer_moore text pattern 0 0)
     else sprintf "The length of the pattern needs to be less or equal to the length of the text!"
  in
  print_string message

#push-options "--warn_error -272"
let _ = main()
#pop-options