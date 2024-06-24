module NewOrOld

open GlobalData
open ItemIndices
open FStar.Classical 
open FStar.IO
open FStar.Printf
open FStar.List
open FStar.List.Tot.Base

let new_or_old (#a:eqtype) (c:a) (l:list a) : int
  = if item_indices c l 0 <> []
    then last (item_indices c l 0)
    else -1

let rec mem_last_list (#a:eqtype) (l:list a)
  : Lemma (requires l <> [])
          (ensures mem (last l) l = true)
  = match l with 
    | [el] -> ()
    | hd :: tl -> mem_last_list tl

let new_or_old_return_values (#a:eqtype) (l:list a) (item:a)
  : Lemma (ensures new_or_old item l = -1 || (new_or_old item l >= 0 && new_or_old item l < length l))
  = if item_indices item l 0 = []
    then ()
    else (
      mem_last_list (item_indices item l 0);
      item_indices_is_in_interval item l 0 (last (item_indices item l 0))
    )

let rec not_new_or_old_empty_list (#a:eqtype) (l:list a) (item:a)
  : Lemma (ensures new_or_old item l = -1 ==> item_indices item l 0 = [])
  = match l with
    | [] -> ()
    | hd :: tl -> not_new_or_old_empty_list tl item 

let rec empty_list_length_zero (#a:eqtype) (l:list a) (item:a)
  : Lemma (ensures item_indices item l 0 = [] ==> length (item_indices item l 0) = 0)
  = match l with 
    | [] -> ()
    | hd :: tl -> empty_list_length_zero tl item

let rec length_zero_count_zero (#a:eqtype) (l:list a) (item:a)
  : Lemma (ensures length (item_indices item l 0) = 0 ==> count item l = 0)
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

let new_or_old_not_item (#a:eqtype) (l:list a) (item:a)
  : Lemma (ensures forall (i:nat{i < length l}). new_or_old item l = -1 ==> index l i <> item)
  = forall_intro (new_or_old_not_item_base l item)   

let rec new_or_old_not_empty_list (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a). new_or_old item l <> -1 ==> item_indices item l 0 <> [])
  = match l with
    | [] -> ()
    | hd :: tl -> new_or_old_not_empty_list tl

let rec not_empty_list_mem_is_true_base (#a:eqtype) (l:list a) (item:a)
  : Lemma (ensures item_indices item l 0 <> [] ==> mem (last (item_indices item l 0)) (item_indices item l 0) = true)
  = match l with
    | [] -> ()
    | hd :: tl -> not_empty_list_mem_is_true_base tl item;
                  if item_indices item l 0 <> []
                  then mem_last_list (item_indices item l 0)
                  else ()

let not_empty_list_mem_is_true (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a). item_indices item l 0 <> [] ==> mem (last (item_indices item l 0)) (item_indices item l 0) = true)
  = forall_intro (not_empty_list_mem_is_true_base l)
 
let mem_index_is_item (#a:eqtype) (item:a) (l:list a)
  : Lemma (requires item_indices item l 0 <> [] && last (item_indices item l 0) < length l)
          (ensures mem (last (item_indices item l 0)) (item_indices item l 0) = true ==> index l (last (item_indices item l 0)) = item)
  = mem_last_list (item_indices item l 0);
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

let index_in_list_is_less_than_last_base (#a:eqtype) (item:a) (l:list a{item_indices item l 0 <> []}) (x:nat)
  : Lemma (ensures mem x (item_indices item l 0) = true ==> x <= last (item_indices item l 0))
  = mem_list_exists_index (item_indices item l 0) x;
    last_index_is_max item l;
    last_is_length_l_minus_one (item_indices item l 0)

let index_in_list_is_less_than_last (#a:eqtype) (item:a) (l:list a{item_indices item l 0 <> []})
  : Lemma (ensures forall (i:nat). mem i (item_indices item l 0) = true ==> i <= last (item_indices item l 0))
  = forall_intro (index_in_list_is_less_than_last_base item l)

let index_greater_than_last_not_item (#a:eqtype) (item:a) (l:list a{item_indices item l 0 <> []}) (i:nat{i < length l})
  : Lemma (ensures i > (last (item_indices item l 0)) ==> index l i <> item)
  = index_is_not_mem_is_not_item_forall_i l item;
    index_in_list_is_less_than_last item l

let mem_index_is_item_last_indices_are_not_item_base (#a:eqtype) (item:a) (l:list a{item_indices item l 0 <> []}) (i:nat{i > (last (item_indices item l 0)) && i < length l})
  : Lemma (ensures mem (last (item_indices item l 0)) (item_indices item l 0) = true ==> index l i <> item)
  = index_greater_than_last_not_item item l i

let mem_index_is_item_last_indices_are_not_item (#a:eqtype) (item:a) (l:list a{item_indices item l 0 <> []})
  : Lemma (ensures mem (last (item_indices item l 0)) (item_indices item l 0) = true ==> (forall (i:nat{i > (last (item_indices item l 0)) && i < length l}). index l i <> item))
  = forall_intro (index_greater_than_last_not_item item l)

let mem_index_is_item_gives_correct_result (#a:eqtype) (l:list a) (item:a)
  : Lemma (requires item_indices item l 0 <> [] && (last (item_indices item l 0)) < length l)
          (ensures mem (last (item_indices item l 0)) (item_indices item l 0) = true ==> index l (last (item_indices item l 0)) = item /\ 
          (forall (i:nat{i > (last (item_indices item l 0)) && i < length l}). index l i <> item))
  = mem_index_is_item item l;
    mem_index_is_item_last_indices_are_not_item item l

let new_or_old_not_empty_list_correct_item (#a:eqtype) (l:list a) (item:a)
  : Lemma (requires item_indices item l 0 <> [] && last (item_indices item l 0) < length l)
          (ensures new_or_old item l <> -1 ==> index l (last (item_indices item l 0)) = item /\ 
          (forall (i:nat{i > (last (item_indices item l 0)) && i < length l}). index l i <> item))
  = new_or_old_not_empty_list l;
    not_empty_list_mem_is_true l;
    mem_index_is_item_gives_correct_result l item