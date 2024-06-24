module ItemIndices

open GlobalData
open FStar.Classical 
open FStar.IO
open FStar.Printf
open FStar.List
open FStar.List.Tot.Base

let rec item_indices (#a:eqtype) (item:a) (l:list a) (i:nat) 
  : list nat
  = match l with 
    | [] -> []
    | hd :: tl -> if hd = item
                  then i :: item_indices item tl (i + 1)
                  else item_indices item tl (i + 1)

let rec item_list_has_correct_length (#a:eqtype) (l:list a) (i:nat)
  : Lemma (ensures forall (item:a). length (item_indices item l i) = count item l)
  = match l with 
    | [] -> ()
    | hd :: tl -> item_list_has_correct_length tl (i + 1)

let rec item_indices_is_in_interval (#a:eqtype) (item:a) (l:list a) (i:nat) (x:nat)
  : Lemma (ensures mem x (item_indices item l i) ==> i <= x && x < i + length l)
  = match l with 
    | [] -> () 
    | hd :: tl -> item_indices_is_in_interval item tl (i + 1) x 

let item_indices_is_in_interval_forall (#a:eqtype) (l:list a) (i:nat) (item:a)
  : Lemma (ensures forall (x:nat). mem x (item_indices item l i) ==> i <= x && x < i + length l)
  = forall_intro (item_indices_is_in_interval item l i)

let item_indices_is_in_interval_forall_item (#a:eqtype) (l:list a) (i:nat)
  : Lemma (ensures forall (item:a) (x:nat). mem x (item_indices item l i) ==> i <= x && x < i + length l)
  = forall_intro (item_indices_is_in_interval_forall l i)

let rec item_indices_one_and_item_indices_zero (#a:eqtype) (item:a) (l:list a) (x:nat{x > 0}) (i:nat{i > 0})
  : Lemma (ensures mem x (item_indices item l i) = mem (x - 1) (item_indices item l (i - 1)))
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
                            assert(mem x (item_indices item l i) = mem x (item_indices item tl (i + 1)));
                            assert(mem (x - 1) (item_indices item l (i - 1)) = mem (x - 1) (item_indices item tl i));
                            item_indices_one_and_item_indices_zero item tl x (i + 1)
                          )
                         )

let rec index_increases_with_one_when_element_is_added (#a:eqtype) (item:a) (l:list a) (i:nat{i > 0}) (el:a)
  : Lemma (ensures mem (i - 1) (item_indices item l 0) = false ==> mem i (item_indices item (el :: l) 0) = false)
  = match l with 
    | [] -> ()
    | hd :: tl -> match i with 
                  | 1 -> if hd = item 
                         then ()
                         else item_indices_is_in_interval item tl 2 1
                  | _ -> item_indices_one_and_item_indices_zero item l i 1;
                         index_increases_with_one_when_element_is_added item tl (i - 1) hd

let rec index_increases_with_one_when_element_is_added_for_true (#a:eqtype) (item:a) (l:list a) (i:nat{i > 0}) (el:a)
  : Lemma (ensures mem (i - 1) (item_indices item l 0) = true ==> mem i (item_indices item (el :: l) 0) = true)
  = match l with 
    | [] -> ()
    | hd :: tl -> match i with 
                  | 1 -> if hd = item 
                         then ()
                         else item_indices_is_in_interval item tl i (i - 1)
                  | _ -> item_indices_one_and_item_indices_zero item l i 1;
                         index_increases_with_one_when_element_is_added_for_true item tl (i - 1) hd

let rec index_increases_with_one_when_first_is_item (#a:eqtype) (item:a) (l:list a) (i:nat{i > 0})
  : Lemma (ensures mem (i - 1) (item_indices item l 0) = false ==> mem i (0 :: item_indices item l 1) = false)
  = match l with 
    | [] -> ()
    | hd :: tl -> match i with 
                  | 1 -> if hd = item 
                         then ()
                         else item_indices_is_in_interval item tl 2 1
                  | _ -> item_indices_one_and_item_indices_zero item l i 1;
                         index_increases_with_one_when_first_is_item item tl (i - 1)

let rec index_increases_with_one_when_first_is_item_for_true (#a:eqtype) (item:a) (l:list a) (i:nat{i > 0})
  : Lemma (ensures mem (i - 1) (item_indices item l 0) = true ==> mem i (0 :: item_indices item l 1) = true)
  = match l with 
    | [] -> ()
    | hd :: tl -> match i with 
                  | 1 -> if hd = item 
                         then ()
                         else item_indices_is_in_interval item tl i (i - 1)
                  | _ -> item_indices_one_and_item_indices_zero item l i 1;
                         index_increases_with_one_when_first_is_item_for_true item tl (i - 1)

let rec index_is_not_item_is_not_mem_base (#a:eqtype) (l:list a) (item:a) (i:nat{i < length l})
  : Lemma (ensures index l i <> item ==> mem i (item_indices item l 0) = false)
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
  : Lemma (ensures forall (item:a) (i:nat{i < length l}). index l i <> item ==> mem i (item_indices item l 0) = false)
  = forall_intro_2 (index_is_not_item_is_not_mem_base l)

let rec index_is_item_is_mem_base (#a:eqtype) (l:list a) (item:a) (i:nat{i < length l})
  : Lemma (ensures index l i = item ==> mem i (item_indices item l 0) = true)
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
  : Lemma (ensures forall (item:a) (i:nat{i < length l}). index l i = item ==> mem i (item_indices item l 0) = true)
  = forall_intro_2 (index_is_item_is_mem_base l)

let rec index_is_not_mem_is_not_item_base (#a:eqtype) (l:list a) (item:a) (i:nat{i < length l})
  : Lemma (ensures mem i (item_indices item l 0) = false ==> index l i <> item)
  = match l with
    | [] -> ()
    | hd :: tl -> match i with 
                  | 0 -> if hd = item 
                         then ()
                         else item_indices_is_in_interval item tl (i + 1) i
                  | _ -> index_is_not_mem_is_not_item_base tl item (i - 1);
                         item_indices_one_and_item_indices_zero item tl i 1

let index_is_not_mem_is_not_item_forall_i (#a:eqtype) (l:list a) (item:a)
  : Lemma (ensures forall (i:nat{i < length l}). mem i (item_indices item l 0) = false ==> index l i <> item)
  = forall_intro (index_is_not_mem_is_not_item_base l item)

let index_is_not_mem_is_not_item (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a) (i:nat{i < length l}). mem i (item_indices item l 0) = false ==> index l i <> item)
  = forall_intro (index_is_not_mem_is_not_item_forall_i l)

let rec index_is_mem_is_item_base (#a:eqtype) (l:list a) (item:a) (i:nat{i < length l})
  : Lemma (ensures mem i (item_indices item l 0) = true ==> index l i = item)
  = match l with
    | [] -> ()
    | hd :: tl -> match i with 
                  | 0 -> if hd = item 
                         then ()
                         else item_indices_is_in_interval item tl (i + 1) i
                  | _ -> index_is_mem_is_item_base tl item (i - 1);
                         item_indices_one_and_item_indices_zero item tl i 1

let index_is_mem_is_item_forall_i (#a:eqtype) (l:list a) (item:a)
  : Lemma (ensures forall (i:nat{i < length l}). mem i (item_indices item l 0) = true ==> index l i = item)
  = forall_intro (index_is_mem_is_item_base l item)

let index_is_mem_is_item (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a) (i:nat{i < length l}). mem i (item_indices item l 0) = true ==> index l i = item)
  = forall_intro (index_is_mem_is_item_forall_i l)

let index_not_mem_not_item_not_item_not_mem (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a) (i:nat{i < length l}). mem i (item_indices item l 0) = false <==> index l i <> item)
  = index_is_not_item_is_not_mem l;
    index_is_not_mem_is_not_item l

let index_mem_item_item_mem (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a) (i:nat{i < length l}). mem i (item_indices item l 0) = true <==> index l i = item)
  = index_is_mem_is_item l;
    index_is_item_is_mem l

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

let rec index_not_zero_not_first_element (#a:eqtype) (l:list a) (item:a) (m:nat) (i:nat{i < length (item_indices item l m)})
  : Lemma (requires length (item_indices item l m) > 1)
          (ensures 
           (let indices = item_indices item l m in
            i <> 0 ==> index indices i <> hd indices))
  = match l with 
    | [] -> ()
    | fst :: tl -> if fst = item 
                   then (
                    assert(hd (item_indices item l m) = m);
                    assert(item_indices item l m = m :: (item_indices item tl (m + 1)));
                    match i with 
                    | 0 -> ()
                    | _ -> mem_index_element (item_indices item tl (m + 1)) (i - 1);
                           item_indices_is_in_interval item tl (m + 1) (index (item_indices item tl (m + 1)) (i - 1))
                   )
                   else index_not_zero_not_first_element tl item (m + 1) i

let rec hd_item_indices_is_min (#a:eqtype) (l:list a) (item:a) (i:nat) (m:nat)
  : Lemma (requires length (item_indices item l m) > 1)
          (ensures 
           (let indices = item_indices item l m in 
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
  : Lemma (ensures item_indices item l m = map subtraction (item_indices item l (m + 1)))
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

let rec indices_are_ordered_in_ascending_order_base (#a:eqtype) (l:list a) (item:a) 
        (i:nat{i < length (item_indices item l 0)}) (j:nat{j < length (item_indices item l 0)})
  : Lemma (requires i < j)
          (ensures 
           (let indices = item_indices item l 0 in
            index indices i < index indices j))
  = match l with 
    | [] -> ()
    | fst :: tl -> let l' = item_indices item l 0 in 
                   let l'' = item_indices item tl 1 in
                   let l''' = item_indices item tl 0 in
                   match i with 
                  | 0 -> if fst = item 
                         then (
                          mem_index_element l'' (j - 1);
                          item_indices_is_in_interval item tl 1 (index l'' (j - 1))
                         )
                         else (
                          if length l'' < 2
                          then ()
                          else (
                            mem_index_element l' j;
                            index_not_zero_not_first_element l item 0 j;
                            hd_item_indices_is_min l item (index l' j) 0
                          )
                         )
                  | _ -> item_indices_zero_is_item_indices_one_minus_one tl item 0;
                         assert(l''' = map subtraction l'');
                         if fst = item
                         then (
                          assert(index l' i = index l'' (i - 1));
                          assert(index l' j = index l'' (j - 1));
                          mem_index_element l'' (i - 1);
                          mem_index_element l'' (j - 1);
                          item_map_subtraction l'' (i - 1);
                          item_map_subtraction l'' (j - 1);
                          item_indices_is_in_interval item tl 1 (index l'' (i - 1));
                          item_indices_is_in_interval item tl 1 (index l'' (j - 1));
                          assert(index l''' (i - 1) = (index l'' (i - 1)) - 1);
                          assert(index l''' (j - 1) = (index l'' (j - 1)) - 1);
                          indices_are_ordered_in_ascending_order_base tl item (i - 1) (j - 1)
                         )
                         else (
                          assert(index l' i = index l'' i);
                          assert(index l' j = index l'' j);
                          mem_index_element l'' i;
                          mem_index_element l'' j;
                          item_map_subtraction l'' i;
                          item_map_subtraction l'' j;
                          item_indices_is_in_interval item tl 1 (index l'' i);
                          item_indices_is_in_interval item tl 1 (index l'' j);
                          assert(index l''' i = (index l'' i) - 1);
                          assert(index l''' j = (index l'' j) - 1);
                          indices_are_ordered_in_ascending_order_base tl item i j 
                         )

let indices_are_ordered_in_ascending_order_implication (#a:eqtype) (l:list a) (item:a)
  (i:nat{i < length (item_indices item l 0)}) (j:nat{j < length (item_indices item l 0)})
  : Lemma (ensures i < j ==>
           (let indices = item_indices item l 0 in
            index indices i < index indices j))
  = move_requires (indices_are_ordered_in_ascending_order_base l item i) j

let indices_are_ordered_in_ascending_order (#a:eqtype) (l:list a) (item:a)
  : Lemma (ensures forall (i:nat{i < length (item_indices item l 0)}) (j:nat{j < length (item_indices item l 0)}). 
           i < j ==>
           (let indices = item_indices item l 0 in
            index indices i < index indices j))
  = forall_intro_2 (indices_are_ordered_in_ascending_order_implication l item)

let indices_are_ordered_in_ascending_order_forall_item (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a) (i:nat{i < length (item_indices item l 0)}) (j:nat{j < length (item_indices item l 0)}). 
           i < j ==>
           (let indices = item_indices item l 0 in
            index indices i < index indices j))
  = forall_intro (indices_are_ordered_in_ascending_order l)

let rec last_is_length_l_minus_one (#a:eqtype) (l:list a)
  : Lemma (requires l <> [])
          (ensures last l = index l ((length l) - 1))
  = match l with
    | [el] -> ()
    | hd :: tl -> last_is_length_l_minus_one tl

let last_index_is_max_base (#a:eqtype) (item:a) (l:list a{item_indices item l 0 <> []}) (i:nat{i < length (item_indices item l 0) - 1})
  : Lemma (ensures 
           (let indices = item_indices item l 0 in
            let j = (length indices) - 1 in
            index indices i < index indices j))
  = indices_are_ordered_in_ascending_order_base l item i (length (item_indices item l 0) - 1)

let last_index_is_max (#a:eqtype) (item:a) (l:list a{item_indices item l 0 <> []}) 
  : Lemma (ensures forall (i:nat{i < length (item_indices item l 0) - 1}).
           (let indices = item_indices item l 0 in
            let j = (length indices) - 1 in
            index indices i < index indices j))
  = forall_intro (last_index_is_max_base item l)