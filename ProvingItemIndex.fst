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

let rec mem_index_element (#a:eqtype) (l:list a) (i:nat{i < length l})
  : Lemma (ensures mem (index l i) l = true)
  = match l with 
    | [] -> ()
    | hd :: tl -> match i with
                  | 0 -> ()
                  | _ -> mem_index_element tl (i - 1)

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

let hd_item_indices_is_min (#a:eqtype) (l:list a) (item:a) (i:nat)
  : Lemma (requires length (item_index item l 0) > 1)
          (ensures 
           (let indices = item_index item l 0 in 
            mem i indices && i <> hd indices ==> i > hd indices))
  = admit()

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
                          // assert(item_index item l 0 = 0 :: item_index item tl 1);
                          // assert(index (item_index item l 0) i = 0);
                          // assert(index (item_index item l 0) j = index (item_index item tl 1) (j - 1));
                          mem_index_element (item_index item tl 1) (j - 1);
                          item_indices_is_in_interval item tl 1 (index (item_index item tl 1) (j - 1))
                         )
                         else (
                          assert(item_index item l 0 = item_index item tl 1);
                          assert(index (item_index item l 0) i = index (item_index item tl 1) i);
                          assert(index (item_index item l 0) j = index (item_index item tl 1) j);
                          assert(index (item_index item tl 1) i = hd (item_index item tl 1));
                          assert(j > 0);
                          assert(j <> i);
                          //assert(index (item_index item tl 1) j <> hd (item_index item tl 1));
                          //assert(index (item_index item tl 1) j = index (item_index item (tail tl) 2) (j - 1));
                          if length (item_index item tl 1) < 2
                          then ()
                          else (
                            mem_index_element (item_index item l 0) j;
                            index_not_zero_not_first_element l item 0 j;
                            hd_item_indices_is_min l item (index (item_index item l 0) j)
                          )
                         )
                  | _ -> admit()

let item_list_length_is_zero_if_the_list_length_is_zero (#a:eqtype) (l:list a)
  : Lemma (requires l = [])
          (ensures forall (item:a). length (item_index item l 0) = 0)
  = ()

let item_head (#a:eqtype) (l:list a)
  : Lemma (requires length l >= 1)
          (ensures forall (item:a). length (item_index item [hd l] 0) <= 1)
  = ()

let rec item_head_not_equal (#a:eqtype) (l:list a)
  : Lemma (requires length l >= 1)
          (ensures forall (item:a). hd l <> item ==> length (item_index item [hd l] 0) = 0)
  = match l with
    | last -> ()
    | hd :: tl -> item_head_not_equal tl

let rec item_head_equal (#a:eqtype) (l:list a)
  : Lemma (requires length l >= 1)
          (ensures forall (item:a). hd l = item ==> length (item_index item [hd l] 0) = 1)
  = match l with
    | last -> ()
    | hd :: tl -> item_head_equal tl

let rec item_head_count (#a:eqtype) (l:list a)
  : Lemma (requires length l >= 1) 
          (ensures forall (item:a). length (item_index item [hd l] 0) = count item [hd l])
  = match l with 
    | last -> ()
    | hd :: tl -> item_head_count tl

let item_empty_list_count (a:eqtype)
  : Lemma (ensures forall (item:a). length (item_index item [] 0) = count item [])
  = ()

let rec item_tail_count (#a:eqtype) (l:list a)
  : Lemma (requires length l >= 1) 
          (ensures forall (item:a). length (item_index item (tl l) 0) = count item (tl l))
  = match l with 
    | last -> admit()
    | hd :: tl -> admit(item_tail_count tl)

let rec item_tail (#a:eqtype) (l:list a)
  : Lemma (requires length l >= 1)
          (ensures forall (item:a). length (item_index item l 0) = length (item_index item [hd l] 0) + length (item_index item (tl l) 1))
  = match l with 
    | final -> ()
    | hd :: tl -> item_tail tl

let rec count_tail (#a:eqtype) (l:list a)
  : Lemma (requires length l >= 1)
          (ensures forall (item:a). count item l = count item [hd l] + count item (tl l))
  = match l with
    | final -> ()
    | hd :: tl -> count_tail tl

let rec item_index_is_empty (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a). (l = []) \/ (forall (i:nat{i < length l}). index l i <> item) ==> item_index item l 0 = [])
  = match l with
    | [] -> ()
    | hd :: tl -> admit(item_index_is_empty tl)

let rec reunite_the_list (#a:eqtype) (l:list a)
  : Lemma (requires length l >= 1)
          (ensures l = append [hd l] (tl l))
  = match l with 
    | final -> ()
    | hd :: tl -> reunite_the_list tl

let rec item_tail_not_equal (#a:eqtype) (l:list a)
  : Lemma (requires length l >= 1)
          (ensures forall (item:a). item_index item l 0 = append (item_index item [hd l] 0) (item_index item (tl l) 1))
  = match l with
    | final -> ()
    | hd :: tl -> item_tail_not_equal tl

let rec item_list_has_length_at_least_zero (#a:eqtype) (l:list a) 
  : Lemma (ensures forall (item:a). length (item_index item l 0) >= 0)
  = match l with
    | [] -> ()
    | hd :: tl -> item_list_has_length_at_least_zero tl

let rec item_has_at_most_length_l_occurrences (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a). count item l <= length l)
  = match l with 
    | [] -> ()
    | hd :: tl -> item_has_at_most_length_l_occurrences tl

//correct store of indexes

let rec exists_item_zero_then_correct_index (#a:eqtype) (l:list a)
  : Lemma (requires length l > 0)
          (ensures forall (item:a).  index l 0 = item ==> mem 0 (item_index item l 0))
  = match l with
    | [last] -> ()
    | hd :: tl -> exists_item_zero_then_correct_index tl

let rec exists_item_one_then_correct_index (#a:eqtype) (l:list a)
  : Lemma (requires length l > 1)
          (ensures forall (item:a).  index l 1 = item ==> mem 1 (item_index item l 0))
  = match length l with
    | 2 -> ()
    | _ -> exists_item_one_then_correct_index (tl l)

let rec exists_item_i_then_correct_index (#a:eqtype) (l:list a) (i:nat)
  : Lemma (requires length l > i)
          (ensures forall (item:a). index l i = item ==> mem i (item_index item l 0))
  = let j = i + 1 in
    match length l with
    | j -> admit()
    | _ -> exists_item_i_then_correct_index (tl l) i

let rec index_is_or_is_not_item_is_or_is_not_mem (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a). forall (i:nat{i < length l}). (index l i = item || index l i <> item) ==> (mem i (item_index item l 0) = true || mem i (item_index item l 0) = false))
  = match l with
    | [] -> ()
    | hd :: tl -> index_is_or_is_not_item_is_or_is_not_mem tl

let rec index_is_not_item_is_not_mem (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a). forall (i:nat{i < length l}). index l i <> item ==> mem i (item_index item l 0) = false)
  = match l with
    | [] -> ()
    | hd :: tl -> admit(index_is_not_item_is_not_mem tl)

let rec exists_item_then_correct_index (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a). forall (i:nat{i < length l}). index l i = item ==> mem i (item_index item l 0))
  = match l with
    | [] -> ()
    | hd :: tl -> admit(exists_item_then_correct_index tl)

let rec correct_index_then_exists_item (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a). forall (n:nat{n < length l}). mem n (item_index item l 0) ==> index l n = item)
  = match l with
    | [] -> ()
    | hd :: tl -> admit(correct_index_then_exists_item tl)

let rec exists_item_index_iff_correct_index (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a). forall (i:nat{i < length l}). index l i = item <==> mem i (item_index item l 0))
  = match l with
    | [] -> ()
    | hd :: tl -> exists_item_index_iff_correct_index tl;
                  exists_item_then_correct_index l;
                  correct_index_then_exists_item l

let rec index_is_in_interval (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a). forall (i:nat). mem i (item_index item l 0) = true ==> i >= 0 && i < length l)
  = match l with 
    | [] -> ()
    | hd :: tl -> admit(index_is_in_interval tl)

let rec last_is_in_interval (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a). item_index item l 0 <> [] ==> last (item_index item l 0) >= 0 && last (item_index item l 0) < length l)
  = match l with
    | [] -> ()
    | hd :: tl -> admit(last_is_in_interval tl)

let new_or_old (#a:eqtype) (c:a) (l:list a) : int
  = if item_index c l 0 <> []
    then last (item_index c l 0)
    else -1

let rec not_new_or_old_empty_list (#a:eqtype) (l:list a) 
  : Lemma (ensures forall (item:a). new_or_old item l = -1 ==> item_index item l 0 = [])
  = match l with
    | [] -> ()
    | hd :: tl -> not_new_or_old_empty_list tl 

let rec empty_list_length_zero (#a:eqtype) (l:list a) 
  : Lemma (ensures forall (item:a). item_index item l 0 = [] ==> length (item_index item l 0) = 0)
  = match l with 
    | [] -> ()
    | hd :: tl -> empty_list_length_zero tl

let rec length_zero_count_zero (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a). length (item_index item l 0) = 0 ==> count item l = 0)
  = match l with
    | [] -> ()
    | hd :: tl -> length_zero_count_zero tl;
                  item_list_has_correct_length l 0

let rec count_zero_mem_false (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a). count item l = 0 ==> mem item l = false)
  = match l with
    | [] -> ()
    | hd :: tl -> count_zero_mem_false tl
                 
let rec mem_false_not_item (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a). mem item l = false ==> (forall (i:nat). i < length l ==> index l i <> item))
  = match l with 
    | [] -> ()
    | hd :: tl -> mem_false_not_item tl

let rec new_or_old_not_item (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a). new_or_old item l = -1 ==> (forall (i:nat). i < length l ==> index l i <> item))
  = match l with
    | [] -> ()
    | hd :: tl -> new_or_old_not_item tl;
                  not_new_or_old_empty_list l;
                  empty_list_length_zero l;
                  length_zero_count_zero l;
                  count_zero_mem_false l;
                  mem_false_not_item l

let rec new_or_old_not_empty_list (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a). new_or_old item l <> -1 ==> item_index item l 0 <> [])
  = match l with
    | [] -> ()
    | hd :: tl -> new_or_old_not_empty_list tl

let rec not_empty_list_length_greater_than_zero (#a:eqtype) (l:list a)
  : Lemma (ensures forall (item:a). (item_index item l 0 <> [] && last (item_index item l 0) < length l) ==> last (item_index item l 0) >= 0)
  = match l with
    | [] -> ()
    | hd :: tl -> not_empty_list_length_greater_than_zero tl                  

let rec last_list_mem (#a:eqtype) (l:list a)
  : Lemma (requires length l > 0)
          (ensures mem (last l) l = true)
  = match l with
    | [hd] -> ()
    | hd :: tl -> last_list_mem tl

let item_index_not_empty (#a:eqtype) (item:a) (l:list a)
  : Type 
  = item_index item l 0 <> []

let implication_last_is_in_list (#a:eqtype) (item:a) (l:list a{item_index item l 0 <> []})
  : Type
  = last (item_index item l 0) >= 0 ==> mem (last (item_index item l 0)) (item_index item l 0) = true

let length_greater_than_zero_mem (#a:eqtype) (item:a) (l:list a)
  : Lemma (requires item_index_not_empty item l)
          (ensures implication_last_is_in_list item l) 
  = last_list_mem (item_index item l 0)

// let length_greater_than_zero_mem_forall (#a:eqtype) (l:list a)
//   : Lemma (ensures forall (item:a). item_index_not_empty ==> implication_last_is_in_list item l)
//   = forall_intro (move_requires (length_greater_than_zero_mem item) l)

let mem_index_is_item (#a:eqtype) (l:list a) (item:a)
  : Lemma (requires item_index item l 0 <> [] && last (item_index item l 0) < length l)
          (ensures mem (last (item_index item l 0)) (item_index item l 0) = true ==> index l (last (item_index item l 0)) = item)
  = exists_item_index_iff_correct_index l;
    ()

let new_or_old_not_empty_list_correct_item (#a:eqtype) (l:list a) (item:a)
  : Lemma (requires item_index item l 0 <> [] && last (item_index item l 0) < length l)
          (ensures new_or_old item l <> -1 ==> index l (last (item_index item l 0)) = item)
  = new_or_old_not_empty_list l;
    not_empty_list_length_greater_than_zero l;
    length_greater_than_zero_mem item l;
    mem_index_is_item l item;
    ()

val update_bc (a:list english_letters) : list int
let rec update_bc a = 
    match a with 
        | [] -> []
        | hd::tl -> (new_or_old hd pattern) :: update_bc tl

let final_bc : list int = update_bc alphabet

let rec final_bc_length_is_alphabet_length (a:list english_letters)
  : Lemma (ensures length (update_bc a) = length a)
  = match a with
      | [] -> ()
      | hd :: tl -> final_bc_length_is_alphabet_length tl