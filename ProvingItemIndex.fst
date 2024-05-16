module ProvingItemIndex 

open FStar.Classical 
open FStar.IO
open FStar.Printf
open FStar.List
open FStar.List.Tot.Base

type english_letters =
  | A
  | B
  | C 
  | D
  | E
  | F 
  | G
  | H
  | I 
  | J
  | K
  | L 
  | M 
  | N 
  | O 
  | P 
  | Q 
  | R 
  | S 
  | T 
  | U 
  | V 
  | W 
  | X 
  | Y 
  | Z

val alphabet : list english_letters 
let alphabet = [A;B;C;D;E;F;G;H;I;J;K;M;N;O;P;Q;R;S;T;U;V;W;X;Y;Z]
  
val text : list english_letters
let text = [E;A;A;A;X;A;B;X;A;A;X;B;A;X;B;A;A;A;B;A;B;B]

val pattern : list english_letters
let pattern = [E;A;A;A;X;E;C;F;C]

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
 
let mem_index_is_item_base (#a:eqtype) (item:a) (l:list a)
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

// let mem_index_is_item_gives_correct_result (#a:eqtype) (item:a) (l:list a{item_index item l 0 <> []})
//   : Lemma (ensures mem (last (item_index item l 0)) (item_index item l 0) = true ==> (forall (i:nat{i > (last (item_index item l 0)) && i < length l}). index l i <> item))

// let new_or_old_not_empty_list_correct_item (#a:eqtype) (l:list a) (item:a)
//   : Lemma (requires item_index item l 0 <> [] && last (item_index item l 0) < length l)
//           (ensures new_or_old item l <> -1 ==> index l (last (item_index item l 0)) = item)
//   = new_or_old_not_empty_list l;
//     not_empty_list_length_greater_than_zero l;
//     length_greater_than_zero_mem item l;
//     mem_index_is_item l item;
//     ()

val update_bc (a:list english_letters) : list int
let rec update_bc a = 
    match a with 
    | [] -> []
    | hd :: tl -> (new_or_old hd pattern) :: update_bc tl

let rec update_bc_length_is_initial_list_length (l:list english_letters)
  : Lemma (ensures length (update_bc l) = length l)
  = match l with 
    | [] -> ()
    | hd :: tl -> update_bc_length_is_initial_list_length tl

let rec update_bc_has_index_minusone_if_letter_is_not_in_pattern_base (l:list english_letters) (i:nat{i < length l && i < length (update_bc l)}) (j:nat{j < length pattern})
  : Lemma (ensures 
           (let l' = update_bc l in
            index l' i = -1 ==> index pattern j <> index l i))
  = update_bc_length_is_initial_list_length l;
    match l with 
    | [] -> ()
    | fst :: tl -> match i with 
                   | 0 -> assert(update_bc l = (new_or_old fst pattern) :: update_bc tl);
                          assert(index (update_bc l) i = new_or_old fst pattern);
                          assert(fst = index l i);
                          new_or_old_not_item_base pattern fst j;
                          assert(new_or_old fst pattern = - 1 ==> index pattern j <> fst)
                   | _ -> update_bc_has_index_minusone_if_letter_is_not_in_pattern_base tl (i - 1) j

let update_bc_has_index_minusone_if_letter_is_not_in_pattern_forall_j (l:list english_letters) (i:nat{i < length l && i < length (update_bc l)})
  : Lemma (ensures forall (j:nat{j < length pattern}).  
           (let l' = update_bc l in
            index l' i = -1 ==> index pattern j <> index l i))
  = forall_intro (update_bc_has_index_minusone_if_letter_is_not_in_pattern_base l i)

let update_bc_has_index_minusone_if_letter_is_not_in_pattern (l:list english_letters)
  : Lemma (ensures forall (i:nat{i < length l && i < length (update_bc l)}). (forall (j:nat{j < length pattern}).  
           (let l' = update_bc l in
            index l' i = -1 ==> index pattern j <> index l i)))
  = forall_intro (update_bc_has_index_minusone_if_letter_is_not_in_pattern_forall_j l)

let final_bc : list int = update_bc alphabet

let rec belongs (t:list english_letters) (p:list english_letters{length p < length t}) (i:nat{i <= (length t) - (length p)})
  : bool 
  = match p with
    | [] -> true
    | hd :: tl -> if hd = index t i 
                  then belongs t tl (i + 1)
                  else false