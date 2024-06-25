module GoodSuffixBeginning

open FStar.Classical 
open FStar.IO
open FStar.Printf
open FStar.List
open FStar.List.Tot.Base
open FStar.List.Tot.Properties
// open ProvingItemIndex

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
let text = [A;B;B;A;X;A;B;X;A;A;X;B;A;X;B;A;A;A;B;A;B;B]

val pattern : (l:list english_letters{l <> []})
let pattern = [A;A;B;A;B;A;A;B]

val alphabet_length : (i:nat{i > 0})
let alphabet_length = length alphabet

let rec recursive_test (i:nat)
  : bool 
  = match i with 
    | 0 -> true 
    | _ -> if length [A;A;A;A;B;B;B;B;A;B;B] <= length text 
           then recursive_test (i - 1)
           else recursive_test 0

// let _ = assert(recursive_test 9 = true)

//equivalent with mem c l 
// val verify_character_in_pattern (c:english_letters) (l:list english_letters) : bool
// let rec verify_character_in_pattern c l =
//     match l with
//         | [] -> false
//         | hd::tl -> if hd = c
//                     then true
//                     else verify_character_in_pattern c tl

//equivalent with map (new_or_old) l
// val change_element_in_bc_list (l:list int) (i:int) (j:int) (n:int) : list int
// let rec change_element_in_bc_list l i j n=
//     match l with
//         | [] -> []
//         | hd::tl -> if i = j
//                     then n::change_element_in_bc_list tl (i + 1) j n
//                     else hd::change_element_in_bc_list tl (i + 1) j n

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

val item_index (#a:eqtype) (item:a) (l:list a) (i:nat{i <= length l}): Tot (i:int{i >= -1}) (decreases i)
let rec item_index item l i
  = match i with 
    | 0 -> -1
    | _ -> if index l (i - 1) = item
           then (i - 1)
           else item_index item l (i - 1)

let length_tail_is_last_index (#a:eqtype) (l:list a) 
  : Lemma (requires length l > 0)
          (ensures length l = 1 + length (tl l))
  = ()

//good suffix part
val first_characters (l:list english_letters) (i:nat{i <= length l}) : list english_letters
let rec first_characters l i =
    match i with 
    | 0 -> []
    | _ -> (index l 0) :: (first_characters (tail l) (i - 1)) 
           
let first_characters_zero_is_empty_list (l:list english_letters)
  : Lemma (ensures first_characters l 0 = [])
  = ()

let rec length_first_characters_i_is_i (l:list english_letters) (i:nat{i <= length l})
  : Lemma (ensures length (first_characters l i) = i)
  = match l with
    | [] -> ()
    | hd :: tl -> match i with 
                  | 0 -> ()
                  | _ -> length_first_characters_i_is_i tl (i - 1)

let rec first_characters_stores_indices_correctly_base (l:list english_letters) (i:nat{i <= length l}) (j:nat{j < i && j < length (first_characters l i)})
  : Lemma (ensures 
           (let l' = first_characters l i in 
            index l' j = index l j))
  = match l with 
    | [] -> ()
    | hd :: tl -> match j with 
                  | 0 -> ()
                  | _ -> first_characters_stores_indices_correctly_base tl (i - 1) (j - 1)

let first_characters_stores_indices_correctly (l:list english_letters) (i:nat{i <= length l})
  : Lemma (ensures forall (j:nat{j < i && j < length (first_characters l i)}).
           (let l' = first_characters l i in 
            index l' j = index l j))
  = forall_intro (first_characters_stores_indices_correctly_base l i)

val last_characters (l:list english_letters) (i:nat{i <= length l}) : list english_letters
let rec last_characters l i =
    match i with
    | 0 -> []
    | _ -> (index l ((length l) - i)) :: (last_characters (tail l) (i - 1))

let last_characters_zero_is_empty_list (l:list english_letters)
  : Lemma (ensures last_characters l 0 = [])
  = ()

let rec length_last_characters_i_is_i (l:list english_letters) (i:nat{i <= length l})
  : Lemma (ensures length (last_characters l i) = i)
  = match l with
    | [] -> ()
    | hd :: tl -> match i with 
                  | 0 -> ()
                  | _ -> length_last_characters_i_is_i tl (i - 1)

// let lemma_aux (l:list english_letters) (i:nat{i > 0 && i <= length l}) (el:english_letters)
//   : Lemma (ensures index l ((length l) - (i - 1))) = index (el :: l) ((length (el :: l)) - i)
//   = admit()

let rec last_characters_stores_indices_correctly_base (l:list english_letters) 
                                                      (i:nat{i <= length l}) (j:nat{j < i && j < length (last_characters l i)})
  : Lemma (ensures 
           (let l' = last_characters l i in 
            index l' j = index l ((length l) - i + j)))
  = match l with 
    | [] -> ()
    | hd :: tl -> match j with 
                  | 0 -> ()
                  | _ -> last_characters_stores_indices_correctly_base tl (i - 1) (j - 1)

let last_characters_stores_indices_correctly (l:list english_letters) 
                                             (i:nat{i <= length l}) 
  : Lemma (ensures forall (j:nat{j < i && j < length (last_characters l i)}).
           (let l' = last_characters l i in 
            index l' j = index l ((length l) - i + j)))
  = forall_intro (last_characters_stores_indices_correctly_base l i)

val compare_frontier (l:list english_letters) (i:nat{i <= length l}) : bool
let compare_frontier l i =
    if first_characters l i = last_characters l i && i < (length l)
    then true
    else false
    
let rec compare_lists_equal_base (l1:list english_letters) (l2:list english_letters) (i:nat{i < length l1 && i < length l2})
  : Lemma (requires l1 = l2)
          (ensures (length l1 = length l2) /\ (index l1 i = index l2 i))
  = match l1 with 
    | [] -> ()
    | hd1 :: tl1 -> match l2 with 
                    | [] -> ()
                    | hd2 :: tl2 -> match i with 
                                    | 0 -> ()
                                    | _ -> compare_lists_equal_base tl1 tl2 (i - 1) 

let compare_lists_equal_implication (l1:list english_letters) (l2:list english_letters) (i:nat{i < length l1 && i < length l2})
  : Lemma (ensures l1 = l2 ==> (length l1 = length l2) /\ (index l1 i = index l2 i))    
  = move_requires (compare_lists_equal_base l1 l2) i           

let compare_lists_equal (l1:list english_letters) (l2:list english_letters)
  : Lemma (ensures l1 = l2 ==> 
                   (length l1 = length l2) /\ (forall (i:nat{i < length l1 && i < length l2}). index l1 i = index l2 i))
  = forall_intro (compare_lists_equal_implication l1 l2)

let rec compare_lists_equal_mutual_base (l1:list english_letters) (l2:list english_letters)
  : Lemma (requires (length l1 = length l2) /\ (forall (i:nat{i < length l1}). index l1 i = index l2 i))
          (ensures l1 = l2)
  = match l1 with 
    | [] -> ()
    | hd1 :: tl1 -> match l2 with 
                    | [] -> ()
                    | hd2 :: tl2 -> assert(length l1 = length l2);
                                    assert(length tl1 = length tl2);
                                    assert(forall (i:nat{i < length l1}). index l1 i = index l2 i);
                                    assert(index l1 0 = index l2 0);
                                    assert(forall (i:nat{i < length l1}). index l1 i = index l2 i);
                                    assert(forall (i:nat{i > 0 && i < length l1}). index l1 i = index tl1 (i - 1));
                                    assert(forall (i:nat{i > 0 && i < length l1}). index l2 i = index tl2 (i - 1));
                                    assert(forall (i:nat{i > 0 && i < length l1}). index tl1 (i - 1) = index tl2 (i - 1));
                                    assert(forall (i:nat{i < length tl1}). index tl1 i = index l1 (i + 1));
                                    compare_lists_equal_mutual_base tl1 tl2

let compare_lists_equal_mutual (l1:list english_letters) (l2:list english_letters)
  : Lemma (ensures (length l1 = length l2) /\ (forall (i:nat{i < length l1}). index l1 i = index l2 i) ==> l1 = l2)  
  = move_requires (compare_lists_equal_mutual_base l1) l2 

let compare_lists_equal_both_parts (l1:list english_letters) (l2:list english_letters)
  : Lemma (ensures l1 = l2 <==> (length l1 = length l2) /\ (forall (i:nat{i < length l1}). index l1 i = index l2 i))  
  = compare_lists_equal l1 l2;
    compare_lists_equal_mutual l1 l2

let compare_lists_not_equal_both_parts (l1:list english_letters) (l2:list english_letters)
  : Lemma (ensures l1 <> l2 <==> (length l1 <> length l2) \/ ((length l1 = length l2) /\ (exists (i:nat{i < length l1}). index l1 i <> index l2 i)))
  = assert(forall (a:Type) (b:Type). (a <==> b) ==> (~a <==> ~b));
    compare_lists_equal_both_parts l1 l2

let compare_frontier_true_i_less_than_length_l (l:list english_letters) (i:nat{i <= length l})
  : Lemma (ensures compare_frontier l i ==> i < length l)
  = ()

let compare_frontier_true_first_characters_are_equal_with_last_characters (l:list english_letters) (i:nat{i <= length l})
  : Lemma (ensures compare_frontier l i = true ==> first_characters l i = last_characters l i)
  = ()

let compare_first_characters_with_last_characters (l:list english_letters) (i:nat{i <= length l})
  : Lemma (ensures forall (j:nat{j < length (first_characters l i) && j < length (last_characters l i)}).
           (let l1 = first_characters l i in
            let l2 = last_characters l i in 
            l1 = l2 ==> (length l1 = length l2) && (index l1 j = index l2 j)))
  = compare_lists_equal (first_characters l i) (last_characters l i)

let compare_frontiers_true_gives_correct_result_base (l:list english_letters) (i:nat{i <= length l})
  : Lemma (ensures
           (let l1 = first_characters l i in
            let l2 = last_characters l i in 
            compare_frontier l i = true ==> 
            (length l1 = length l2) /\ 
            (forall (j:nat{j < length (first_characters l i) && j < length (last_characters l i)}). index l1 j = index l2 j) /\ 
            i < length l))
  = // compare_frontier_true_i_less_than_length_l l i
    // compare_frontier_true_first_characters_are_equal_with_last_characters l i
    // compare_first_characters_with_last_characters l i
    ()

let compare_frontiers_true_gives_correct_result (l:list english_letters) 
  : Lemma (ensures forall (i:nat{i <= length l}).
           (let l1 = first_characters l i in
            let l2 = last_characters l i in 
            compare_frontier l i = true ==> 
            (length l1 = length l2) /\ 
            (forall (j:nat{j < length (first_characters l i) && j < length (last_characters l i)}). index l1 j = index l2 j) /\ 
            i < length l))
  = forall_intro (compare_frontiers_true_gives_correct_result_base l)

let logical_implication (a:Type) (b:Type)
  : Lemma (ensures (a <==> b) ==> (~a <==> ~b))
  = ()

let lists_are_not_equal_base (l1:list english_letters) (l2:list english_letters) 
  : Lemma (requires l1 <> l2)
          (ensures (length l1 <> length l2) \/ 
                   (length l1 = length l2 /\ (exists (i:nat{i < length l1 && i < length l2}). index l1 i <> index l2 i)))
  = compare_lists_not_equal_both_parts l1 l2

let lists_are_not_equal_implication (l1:list english_letters) (l2:list english_letters)
  : Lemma (ensures l1 <> l2 ==> (length l1 <> length l2) \/ 
                                (length l1 = length l2 /\ (exists (i:nat{i < length l1 && i < length l2}). index l1 i <> index l2 i)))
  = move_requires (lists_are_not_equal_base l1) l2

let compare_first_characters_with_last_characters_false (l:list english_letters) (i:nat{i <= length l})
  : Lemma (ensures 
           (let l1 = first_characters l i in
            let l2 = last_characters l i in 
            l1 <> l2 ==> (length l1 <> length l2) \/ 
                         ((length l1 = length l2) /\ (exists (j:nat{j < length l1 && j < length l2}). index l1 j <> index l2 j))))
  = lists_are_not_equal_implication (first_characters l i) (last_characters l i)

let compare_frontiers_false_gives_correct_result_base (l:list english_letters) (i:nat{i <= length l})
  : Lemma (ensures 
           (let l1 = first_characters l i in
            let l2 = last_characters l i in 
            compare_frontier l i = false ==> 
            (length l1 <> length l2) \/
            ((length l1 = length l2) /\ (exists (j:nat{j < length l1 && j < length l2}). index l1 j <> index l2 j)) \/
            (l1 = l2 /\ i >= length l)))
  = compare_first_characters_with_last_characters_false l i

let compare_frontiers_false_gives_correct_result (l:list english_letters) 
  : Lemma (ensures forall (i:nat{i <= length l}).
           (let l1 = first_characters l i in
            let l2 = last_characters l i in 
            compare_frontier l i = false ==> 
            (length l1 <> length l2) \/
            ((length l1 = length l2) /\ (exists (j:nat{j < length l1 && j < length l2}). index l1 j <> index l2 j)) \/
            (l1 = l2 /\ i >= length l)))
  = forall_intro (compare_frontiers_false_gives_correct_result_base l)

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

val maximum_frontier (l:list english_letters) (i:nat{i <= length l}) : nat
let rec maximum_frontier l i =
    match i with
        | 0 -> 0
        | _ -> if compare_frontier l i = true
               then i
               else maximum_frontier l (i - 1)

let rec maximum_frontier_max_value (l:list english_letters{l <> []}) (i:nat{i <= length l})
  : Lemma (ensures maximum_frontier l i < length l)
  = match i with 
    | 0 -> ()
    | _ -> if compare_frontier l i = true 
           then ()
           else maximum_frontier_max_value l (i - 1)

let rec maximum_frontier_value (l:list english_letters) (i:nat{i <= length l})
  : Lemma (ensures maximum_frontier l i <= i)
  = match i with
    | 0 -> ()
    | _ -> if compare_frontier l i = true 
           then ()
           else maximum_frontier_value l (i - 1)

//pass
let rec length_init_list_is_length_list_minus_one (l:list english_letters)
  : Lemma (requires l <> [])
          (ensures length (init l) = length l - 1)
  = match l with 
    | [el] -> ()
    | hd :: tl -> length_init_list_is_length_list_minus_one tl

//pass
let rec maximum_frontier_for_l_and_tail_l (l:list english_letters)
  : Lemma (requires l <> [])
          (ensures maximum_frontier l (length l) = maximum_frontier (init l) (length (init l)))
          (decreases length l)
  = match l with 
    | [el] -> ()
    | _ -> length_init_list_is_length_list_minus_one l;
           maximum_frontier_for_l_and_tail_l (init l);
           admit()

let maximum_frontier_zero_no_frontier_for_i (l:list english_letters) (i:nat{i > 0 && i <= length l})
  : Lemma (requires maximum_frontier l i = 0)
          (ensures 
          (let l1 = first_characters l i in 
           let l2 = last_characters l i in 
           (length l1 <> length l2) \/ 
           ((length l1 = length l2) /\ (exists (j:nat{j < length l1 && j < length l2}). index l1 j <> index l2 j)) \/
           i >= length l))
           (decreases length l)
  = compare_frontiers_false_gives_correct_result l

let rec maximum_frontier_zero_for_length_l_and_i_base_general (l:list english_letters) (i:nat{i <= length l}) (j:nat{j <= i})
  : Lemma (requires maximum_frontier l i = 0)
          (ensures maximum_frontier l j = 0)
  = if j = i 
    then ()
    else maximum_frontier_zero_for_length_l_and_i_base_general l (i - 1) j

let maximum_frontier_zero_for_length_l_and_i_base (l:list english_letters) (j:nat{j <= length l})
  : Lemma (requires maximum_frontier l (length l) = 0)
          (ensures maximum_frontier l j = 0)
  = maximum_frontier_zero_for_length_l_and_i_base_general l (length l) j

let maximum_frontier_zero_for_length_l_and_i_implication (l:list english_letters) (j:nat{j <= length l})
  : Lemma (ensures maximum_frontier l (length l) = 0 ==> maximum_frontier l j = 0)
  = move_requires (maximum_frontier_zero_for_length_l_and_i_base l) j 

let maximum_frontier_zero_for_length_l_and_i (l:list english_letters)
  : Lemma (ensures forall (j:nat{j <= length l}). maximum_frontier l (length l) = 0 ==> maximum_frontier l j = 0)
  = forall_intro (maximum_frontier_zero_for_length_l_and_i_implication l)

let maximum_frontier_zero_no_frontier_base (l:list english_letters) (i:nat{i > 0 && i <= length l})
  : Lemma (requires maximum_frontier l (length l) = 0)
          (ensures 
          (let l1 = first_characters l i in 
           let l2 = last_characters l i in 
           (length l1 <> length l2) \/ 
           ((length l1 = length l2) /\ (exists (j:nat{j < length l1 && j < length l2}). index l1 j <> index l2 j)) \/
           i >= length l))
           (decreases length l)
  = maximum_frontier_zero_for_length_l_and_i l;
    maximum_frontier_zero_no_frontier_for_i l i 

let maximum_frontier_zero_no_frontier_implication (l:list english_letters) (i:nat{i > 0 && i <= length l})
  : Lemma (ensures maximum_frontier l (length l) = 0 ==>
           (let l1 = first_characters l i in 
           let l2 = last_characters l i in 
           (length l1 <> length l2) \/ 
           ((length l1 = length l2) /\ (exists (j:nat{j < length l1 && j < length l2}). index l1 j <> index l2 j)) \/
           i >= length l))
  = move_requires (maximum_frontier_zero_no_frontier_base l) i 

let maximum_frontier_zero_no_frontier (l:list english_letters)
  : Lemma (ensures forall (i:nat{i > 0 && i <= length l}). maximum_frontier l (length l) = 0 ==>
           (let l1 = first_characters l i in 
           let l2 = last_characters l i in 
           (length l1 <> length l2) \/ 
           (length l1 = length l2) \/ (exists (j:nat{j < length l1 && j < length l2}). index l1 j <> index l2 j) \/
           i >= length l))
  = forall_intro (maximum_frontier_zero_no_frontier_implication l)

let rec maximum_frontier_i_then_compare_frontier_true (l:list english_letters) (i:nat{i > 0 && i <= length l})
  : Lemma (ensures maximum_frontier l i = i ==> compare_frontier l i = true)
  = match i with 
    | 1 -> ()
    | _ -> if compare_frontier l i = true 
           then ()
           else (
            assert(maximum_frontier l i = maximum_frontier l (i - 1));
            maximum_frontier_value l (i - 1);
            assert(maximum_frontier l (i - 1) <= i - 1);
            maximum_frontier_i_then_compare_frontier_true l (i - 1)
           )

let rec maximum_frontier_not_zero_has_compare_frontier_true (l:list english_letters) (i:nat{i > 0 && i <= length l})
  : Lemma (requires maximum_frontier l i <> 0 && maximum_frontier l i <= length l)
          (ensures 
          (let j = maximum_frontier l i in 
           compare_frontier l j = true))
  = let j = maximum_frontier l i in 
    if j = i 
    then maximum_frontier_i_then_compare_frontier_true l i
    else maximum_frontier_not_zero_has_compare_frontier_true l (i - 1)

let maximum_frontier_not_zero_equal_lists (l:list english_letters) (i:nat{i > 0 && i <= length l})
  : Lemma (requires maximum_frontier l i <> 0 && maximum_frontier l i <= length l)
          (ensures 
          (let x = maximum_frontier l i in 
           let l1 = first_characters l x in 
           let l2 = last_characters l x in 
           l1 = l2 && x < length l))
  = maximum_frontier_not_zero_has_compare_frontier_true l i;
    compare_frontiers_true_gives_correct_result l

let maximum_frontier_not_i_then_compare_frontier_false (l:list english_letters) (i:nat{i <= length l})
  : Lemma (ensures maximum_frontier l i <> i ==> compare_frontier l i = false)
  = ()

let rec maximum_frontier_i_then_compare_frontier_false_if_greater_than_i (l:list english_letters) (i:nat{i <= length l})
                                                                         (i':nat)
  : Lemma (requires i' > maximum_frontier l i && i' <= i)
          (ensures compare_frontier l i' = false)
  = if i = i'
    then maximum_frontier_not_i_then_compare_frontier_false l i'
    else maximum_frontier_i_then_compare_frontier_false_if_greater_than_i l (i - 1) i'

let maximum_frontier_not_zero_not_equal_rest_of_the_lists_base (l:list english_letters) (i:nat{i > 0 && i <= length l})
                                                               (i':nat{i' > maximum_frontier l i && i' <= i && i' < length l})
  : Lemma (ensures 
          (let l1 = first_characters l i' in 
           let l2 = last_characters l i' in 
           l1 <> l2))
  = maximum_frontier_i_then_compare_frontier_false_if_greater_than_i l i i';
    compare_frontiers_false_gives_correct_result l 

let maximum_frontier_not_zero_not_equal_rest_of_the_lists (l:list english_letters) (i:nat{i > 0 && i <= length l})
  : Lemma (ensures forall (i':nat{i' > maximum_frontier l i && i' <= i && i' < length l}).
          (let l1 = first_characters l i' in 
           let l2 = last_characters l i' in 
           l1 <> l2))
  = forall_intro (maximum_frontier_not_zero_not_equal_rest_of_the_lists_base l i)

let maximum_frontier_not_zero_correct_value (l:list english_letters) (i:nat{i > 0 && i <= length l})
  : Lemma (requires maximum_frontier l i <> 0 && maximum_frontier l i <= length l)
          (ensures 
          (let x = maximum_frontier l i in 
           let l1 = first_characters l x in 
           let l2 = last_characters l x in 
           l1 = l2 /\ 
           (forall (i':nat{i' > maximum_frontier l i && i' < i && i' < length l}). 
            let l3 = first_characters l i' in 
            let l4 = last_characters l i' in 
            l3 <> l4)))
  = maximum_frontier_not_zero_equal_lists l i;
    maximum_frontier_not_zero_not_equal_rest_of_the_lists l i

// let rev_stores_correct_indices (#a:eqtype) (l:list a) (i:nat{i < length l})
//   : Lemma (requires length l = length (rev l))
//           (ensures index l i = index (rev l) (length l - 1 - i))
//   = assert(rev l = rev_acc l []);
//     assert(rev_acc l [] = rev_acc (tail l) [hd l])
    // assert(rev_acc (tail l) [hd l] = rev_acc [] ((last l) :: (init l)))

// let rec tail_rev_is_init_l (#a:eqtype) (l:list a{l <> []})
//   : Lemma (requires length l = length (rev l))
//           (ensures tail (rev l) = rev (init l))
//   = match l with 
//     | [el] -> ()
//     | fst :: ot -> rev_length ot; 
//                    tail_rev_is_init_l ot 

let rec create_pr (l:list english_letters) (i:nat{i > 0 && i <= length l})
  : Tot (list int) 
  (decreases length l - i)
  = if i = length l 
    then [maximum_frontier (first_characters l i) (length (first_characters l i))]
    else (maximum_frontier (first_characters l i) (length (first_characters l i))) :: (create_pr l (i + 1))

let rec create_pr_has_same_length_as_initial_list_general (l:list english_letters) (i:nat{i > 0 && i <= length l})
  : Lemma (ensures
          (let l' = create_pr l i in 
           length l' = length l + 1 - i))
          (decreases length l - i)
  = if i = length l 
    then () 
    else create_pr_has_same_length_as_initial_list_general l (i + 1)

let create_pr_has_same_length_as_initial_list_base (l:list english_letters{l <> []})
  : Lemma (ensures
          (let l' = create_pr l 1 in 
           length l' = length l))
  = create_pr_has_same_length_as_initial_list_general l 1

let create_pr_has_same_length_as_initial_list ()
  : Lemma (ensures forall (l:list english_letters{l <> []}).
          (let l' = create_pr l 1 in 
           length l' = length l))
  = forall_intro (create_pr_has_same_length_as_initial_list_base)

let length_equal_then_length_tail_equal (l1:list english_letters{l1 <> []}) (l2:list english_letters{l2 <> []})
  : Lemma (requires length l1 = length l2)
          (ensures length (tail l1) = length (tail l2))
  = ()

let create_pr_tail (l:list english_letters{l <> []}) (i:nat{i > 0 && i < length l})
  : Lemma (ensures create_pr l (i + 1) = tail (create_pr l i))
  = ()

let rec create_pr_values_are_in_correct_index_base (l:list english_letters{l <> []}) 
                                                   (i:nat{i > 0 && i <= length l}) (j:nat{j < length (create_pr l i)})
  : Lemma (ensures 
          (let l' = create_pr l i in 
           index l' j >= 0 && index l' j < i + j))
           (decreases length l - i)
  = if j = 0
    then (
      length_first_characters_i_is_i l i;
      first_characters_stores_indices_correctly l i;
      maximum_frontier_max_value (first_characters l i) i
    )
    else (
      assert(index (create_pr l i) j = index (tail (create_pr l i)) (j - 1));
        assert(index (create_pr l i) j = index (create_pr l (i + 1)) (j - 1));
        create_pr_has_same_length_as_initial_list_general l i;
        create_pr_has_same_length_as_initial_list_general l (i + 1);
        assert(j < length (create_pr l i));
        assert(j < length l + 1 - i);
        assert(j - 1 < length l - i);
        create_pr_values_are_in_correct_index_base l (i + 1) (j - 1);
        assert(index (create_pr l (i + 1)) (j - 1) >= 0 && index (create_pr l (i + 1)) (j - 1) < (i + j))
    )

let create_pr_values_are_in_correct_index_forall_j (l:list english_letters{l <> []}) (i:nat{i > 0 && i <= length l})
  : Lemma (ensures forall (j:nat{j < length (create_pr l i)}). 
          (let l' = create_pr l i in 
           index l' j >= 0 && index l' j < i + j))
  = forall_intro (create_pr_values_are_in_correct_index_base l i) 

let create_pr_values_are_in_correct_index (l:list english_letters{l <> []})
  : Lemma (ensures forall (i:nat{i > 0 && i <= length l}) (j:nat{j < length (create_pr l i)}). 
          (let l' = create_pr l i in 
           index l' j >= 0 && index l' j < i + j))
  = forall_intro (create_pr_values_are_in_correct_index_forall_j l)

// let rec go_through_rev_create_pr (l:list english_letters{l <> []}) 
//                                  (i:nat{i > 0 && i <= length l}) (j:nat{j < length (create_pr l i)})
//   : Lemma (requires length (create_pr l i) = length (rev (create_pr l i)) && length (create_pr l i) = length l + 1 - i)
//           (ensures 
//           (let l' = rev (create_pr l i) in 
//            index l' j = maximum_frontier (first_characters l (length l - j)) (length (first_characters l (length l - j)))))
//   = if j = 0 
//     then admit()
//     else go_through_rev_create_pr l i (j - 1)

// let rec rev_create_pr_values_are_in_correct_index_base (l:list english_letters{l <> []}) 
//                                                        (i:nat{i > 0 && i <= length l}) (j:nat{j < length (create_pr l i)})
//   : Lemma (requires length (create_pr l i) = length (rev (create_pr l i)))
//           (ensures 
//           (let l' = rev (create_pr l i) in 
//            index l' j >= 0 && index l' j < i + j))
//           (decreases length l - i)
  // = if j = 0
  //   then (
  //     rev_mem (create_pr l i) (index (create_pr l i) j);
  //     length_first_characters_i_is_i l i;
  //     first_characters_stores_indices_correctly l i;
  //     maximum_frontier_max_value (first_characters l i) i;
  //     admit()
  //   )
  //   else (
  //     rev_length (create_pr l (i + 1));
  //     tail_rev_l_is_rev_tl (create_pr l i);
  //     rev_create_pr_values_are_in_correct_index_base l (i + 1) (j - 1)
  //   )

let rec create_pr_gives_correct_result_base (l:list english_letters{l <> []}) 
                                            (i:nat{i > 0 && i <= length l}) 
                                            (j:nat{j < length (create_pr l i)})
  : Lemma (requires length (create_pr l i) = length l + 1 - i)
          (ensures
          (let l' = create_pr l i in 
           let x = index l' j in 
           x = maximum_frontier (first_characters l (i + j)) (length (first_characters l (i + j)))))
          (decreases j)
  = if j = 0 
    then ()
    else (
      create_pr_has_same_length_as_initial_list_general l (i + 1);
      assert(length (create_pr l (i + 1)) = length l + 1 - (i + 1));
      assert(create_pr l i = (maximum_frontier (first_characters l i) (length (first_characters l i))) :: (create_pr l (i + 1)));
      assert(index (create_pr l i) j = index (tail (create_pr l i)) (j - 1));
      assert(index (tail (create_pr l i)) (j - 1) = index (create_pr l (i + 1)) (j - 1));
      assert(j < length l + 1 - i);
      assert(j + i < length l + 1);
      assert(j + i <= length l);
      assert(j - 1 < length l + 1 - (i + 1));
      assert(j - 1 < length l - i);
      assert(j + i < length l + 1);
      assert(j + i <= length l);
      create_pr_gives_correct_result_base l (i + 1) (j - 1)
    )

let create_pr_gives_correct_result_implication (l:list english_letters{l <> []}) 
                                               (i:nat{i > 0 && i <= length l}) 
                                               (j:nat{j < length (create_pr l i)})
  : Lemma (ensures length (create_pr l i) = length l + 1 - i ==> 
          (let l' = create_pr l i in 
           let x = index l' j in 
           x = maximum_frontier (first_characters l (i + j)) (length (first_characters l (i + j)))))
  = create_pr_has_same_length_as_initial_list_general l i;
    move_requires (create_pr_gives_correct_result_base l i) j 

let create_pr_gives_correct_result_forall_j (l:list english_letters{l <> []}) 
                                                        (i:nat{i > 0 && i <= length l}) 
  : Lemma (ensures forall (j:nat{j < length (create_pr l i)}). length (create_pr l i) = length l + 1 - i ==> 
          (let l' = create_pr l i in 
           let x = index l' j in 
           x = maximum_frontier (first_characters l (i + j)) (length (first_characters l (i + j)))))
  = forall_intro (create_pr_gives_correct_result_implication l i)

let create_pr_gives_correct_result (l:list english_letters{l <> []}) 
  : Lemma (ensures forall (i:nat{i > 0 && i <= length l})  (j:nat{j < length (create_pr l i)}). 
           length (create_pr l i) = length l + 1 - i ==> 
          (let l' = create_pr l i in 
           let x = index l' j in 
           x = maximum_frontier (first_characters l (i + j)) (length (first_characters l (i + j)))))
  = forall_intro (create_pr_gives_correct_result_forall_j l)

let f : list int = create_pr pattern 1

let create_pr_has_same_length_as_initial_list_for_pattern ()
  : Lemma (ensures length f = length pattern)
  = create_pr_has_same_length_as_initial_list_base pattern

let create_pr_values_are_in_correct_index_for_pattern ()
  : Lemma (ensures forall (j:nat{j < length f}). 
           index f j >= 0 && index f j < 1 + j)
  = create_pr_values_are_in_correct_index_forall_j pattern 1

let create_pr_gives_correct_result_for_pattern ()
  : Lemma (ensures forall (j:nat{j < length f}). length f = length pattern ==> 
          (let x = index f j in 
           x = maximum_frontier (first_characters pattern (1 + j)) (length (first_characters pattern (1 + j)))))
  = create_pr_gives_correct_result_forall_j pattern 1

// val give_value (f:list int) (nr:int) (i:nat{i >= 0}) : int
// let rec give_value f nr i =
//     match f with
//         | [] -> -1
//         | hd::tl -> if i = nr
//                     then hd
//                     else give_value tl nr (i + 1)

let rec substring (#a:eqtype) (l:list a) (i:nat{i < length l}) (j:nat{j >= i && j < length l})
  : Tot (list a) 
  (decreases length l - i)
  = if i = j 
    then [index l i]
    else (index l i) :: substring l (i + 1) j

let rec substring_list_length (#a:eqtype) (l:list a) (i:nat{i < length l}) (j:nat{j >= i && j < length l})
  : Lemma (ensures length (substring l i j) = j - i + 1)
  (decreases length l - i)
  = if i = j 
    then ()
    else substring_list_length l (i + 1) j

let rec substring_stores_correct_values_base (#a:eqtype) (l:list a) (i:nat{i < length l}) (j:nat{j >= i && j < length l}) (k:nat{k >= i && k <= j})
  : Lemma (requires k - i < length (substring l i j))
          (ensures 
          (let l' = substring l i j in 
           index l k = index l' (k - i)))
          (decreases length l - i)
  = if i = k 
    then ()
    else substring_stores_correct_values_base l (i + 1) j k

let substring_stores_correct_values_implication (#a:eqtype) (l:list a) (i:nat{i < length l}) (j:nat{j >= i && j < length l}) (k:nat{k >= i && k <= j})
  : Lemma (ensures 
          (let l' = substring l i j in 
           k - i < length (substring l i j) ==> index l k = index l' (k - i)))
  = substring_list_length l i j;
    move_requires (substring_stores_correct_values_base l i j) k

let substring_stores_correct_values (#a:eqtype) (l:list a) (i:nat{i < length l}) (j:nat{j >= i && j < length l}) 
  : Lemma (ensures forall (k:nat{k >= i && k <= j}).
          (let l' = substring l i j in 
           k - i < length (substring l i j) ==> index l k = index l' (k - i)))
  = forall_intro (substring_stores_correct_values_implication l i j)

let rec create_gs (l:list english_letters) (i:nat{i <= length l}) 
  : Tot (list int) 
  (decreases length l - i)
  = if i = length l
    then [] 
    else (
      create_pr_has_same_length_as_initial_list_base l;
      (index (create_pr l 1) (length l - 1) - (length l - i)) :: (create_gs l (i + 1))
    )

let rec create_gs_length_is_l_length_general (l:list english_letters) (i:nat{i <= length l})  
  : Lemma (ensures 
          (let l' = create_gs l i in 
           length l' = length l - i))
          (decreases length l - i)
  = if i = length l 
    then ()
    else create_gs_length_is_l_length_general l (i + 1)

let create_gs_length_is_l_length_base (l:list english_letters)
  : Lemma (ensures 
          (let l' = create_gs l 0 in 
           length l' = length l))
  = create_gs_length_is_l_length_general l 0

let create_gs_length_is_l_length ()
  : Lemma (ensures forall (l:list english_letters).
          (let l' = create_gs l 0 in 
           length l' = length l))
  = forall_intro create_gs_length_is_l_length_base

let rec create_gs_values_general (l:list english_letters) (i:nat{i < length l}) (j:nat{j < length l - i})
  : Lemma (requires length (create_pr l 1) = length l && length (create_gs l i) = length l - i)
          (ensures 
          (let l' = create_gs l i in 
           index l' j = index (create_pr l 1) (length l - 1) - (length l - (i + j))))
          (decreases length l - i)
  = if j = 0 
    then ()
    else (
      create_pr_has_same_length_as_initial_list_base l;
      create_gs_length_is_l_length_general l (i + 1);
      assert(create_gs l i = (index (create_pr l 1) (length l - 1) - (length l - i)) :: (create_gs l (i + 1)));
      assert(index (create_gs l i ) j = index (tail (create_gs l i)) (j - 1));
      assert(tail (create_gs l i) = create_gs l (i + 1));
      assert(index (create_gs l i ) j = index (create_gs l (i + 1)) (j - 1));
      create_gs_values_general l (i + 1) (j - 1)
    )
        
let create_gs_values_base (l:list english_letters) (i:nat{i < length l}) (j:nat{j < length l - i})
  : Lemma (ensures length (create_pr l 1) = length l && length (create_gs l i) = length l - i ==> 
          (let l' = create_gs l i in 
           index l' j = index (create_pr l 1) (length l - 1) - (length l - (i + j))))
  = create_pr_has_same_length_as_initial_list_base l;
    create_gs_length_is_l_length_general l i;
    move_requires (create_gs_values_general l i) j

let create_gs_values_forall_j (l:list english_letters) (i:nat{i < length l})
  : Lemma (ensures forall (j:nat{j < length l - i}).
           length (create_pr l 1) = length l && length (create_gs l i) = length l - i ==> 
          (let l' = create_gs l i in 
           index l' j = index (create_pr l 1) (length l - 1) - (length l - (i + j))))
  = forall_intro (create_gs_values_base l i)

let create_gs_values (l:list english_letters)
  : Lemma (ensures forall (i:nat{i < length l}) (j:nat{j < length l - i}).
           length (create_pr l 1) = length l && length (create_gs l i) = length l - i ==> 
          (let l' = create_gs l i in 
           index l' j = index (create_pr l 1) (length l - 1) - (length l - (i + j))))
  = forall_intro (create_gs_values_forall_j l)

let rec append (#a:eqtype) (l1:list a) (l2:list a)
  : list a 
  = match l1 with 
    | [] -> l2 
    | hd :: tl -> hd :: (append tl l2)

let rec append_length (#a:eqtype) (l1:list a) (l2:list a)
  : Lemma (ensures length (append l1 l2) = length l1 + length l2)
  = match l1 with 
    | [] -> ()
    | hd :: tl -> append_length tl l2 

let rec append_indices_from_first_list_are_stored_correctly_base (#a:eqtype) (l1:list a) (l2:list a) (i:nat{i < length l1})
  : Lemma (requires length (append l1 l2) = length l1 + length l2)
          (ensures index (append l1 l2) i = index l1 i)
  = if i = 0 
    then ()
    else append_indices_from_first_list_are_stored_correctly_base (tail l1) l2 (i - 1)

let append_indices_from_first_list_are_stored_correctly_implication (#a:eqtype) (l1:list a) (l2:list a) (i:nat{i < length l1})
  : Lemma (ensures length (append l1 l2) = length l1 + length l2 ==> index (append l1 l2) i = index l1 i)
  = append_length l1 l2;
    move_requires (append_indices_from_first_list_are_stored_correctly_base l1 l2) i

let append_indices_from_first_list_are_stored_correctly (#a:eqtype) (l1:list a) (l2:list a)
  : Lemma (ensures forall (i:nat{i < length l1}). length (append l1 l2) = length l1 + length l2 ==> index (append l1 l2) i = index l1 i)
  = forall_intro (append_indices_from_first_list_are_stored_correctly_implication l1 l2)

let rec append_indices_from_second_list_are_stored_correctly_base (#a:eqtype) (l1:list a) (l2:list a) 
                                                                  (i:nat{i >= length l1 && i < length l1 + length l2})
  : Lemma (requires length (append l1 l2) = length l1 + length l2)
          (ensures index (append l1 l2) i = index l2 (i - length l1))
  = if length l1 = 0 
    then ()
    else append_indices_from_second_list_are_stored_correctly_base (tail l1) l2 (i - 1)

let append_indices_from_second_list_are_stored_correctly_implication (#a:eqtype) (l1:list a) (l2:list a) 
                                                                     (i:nat{i >= length l1 && i < length l1 + length l2})
  : Lemma (ensures length (append l1 l2) = length l1 + length l2 ==> index (append l1 l2) i = index l2 (i - length l1))
  = append_length l1 l2;
    move_requires (append_indices_from_second_list_are_stored_correctly_base l1 l2) i

let append_indices_from_second_list_are_stored_correctly (#a:eqtype) (l1:list a) (l2:list a) 
  : Lemma (ensures forall (i:nat{i >= length l1 && i < length l1 + length l2}). 
           length (append l1 l2) = length l1 + length l2 ==> index (append l1 l2) i = index l2 (i - length l1))
  = forall_intro (append_indices_from_second_list_are_stored_correctly_implication l1 l2)

let append_indices_are_stored_correctly (#a:eqtype) (l1:list a) (l2:list a) 
  : Lemma (ensures forall (i:nat{i < length l1}) (j:nat{j >= length l1 && j < length l1 + length l2}). 
           length (append l1 l2) = length l1 + length l2 ==> 
           index (append l1 l2) i = index l1 i && index (append l1 l2) j = index l2 (j - length l1))
  = append_indices_from_first_list_are_stored_correctly l1 l2;
    append_indices_from_second_list_are_stored_correctly l1 l2

let rec reverse (#a:eqtype) (l:list a)
  : list a 
  = match l with 
    | [] -> []
    | hd :: tl -> append (reverse tl) [hd] 

let rec reverse_length_is_l_length (#a:eqtype) (l:list a)
  : Lemma (ensures length l = length (reverse l))
  = match l with 
    | [] -> ()
    | hd :: tl -> reverse_length_is_l_length tl;
                  append_length (reverse tl) [hd]

let rec last_from_append_is_init (#a:eqtype) (l:list a) (el:a)
  : Lemma (ensures init (append l [el]) = l)
  = match l with 
    | [] -> ()
    | hd :: tl -> last_from_append_is_init tl el

//repeated
let rec length_init_list (#a:eqtype) (l:list a)
  : Lemma (requires l <> [])
          (ensures length (init l) = length l - 1)
  = match l with 
    | [el] -> ()
    | hd :: tl -> length_init_list tl

let rec init_l_has_same_indices_except_last_base (#a:eqtype) (l:list a{length l > 1}) (i:nat{i < length l - 1})
  : Lemma (requires length (init l) = length l - 1)
          (ensures index l i = index (init l) i)
  = if i = 0
    then ()
    else (
      length_init_list (tail l);
      init_l_has_same_indices_except_last_base (tail l) (i - 1)
    )

let init_l_has_same_indices_except_last_implication (#a:eqtype) (l:list a{length l > 1}) (i:nat{i < length l - 1})
  : Lemma (ensures length (init l) = length l - 1 ==> index l i = index (init l) i)
  = length_init_list l;
    move_requires (init_l_has_same_indices_except_last_base l) i

let init_l_has_same_indices_except_last (#a:eqtype) (l:list a{length l > 1})
  : Lemma (ensures forall (i:nat{i < length l - 1}). length (init l) = length l - 1 ==> index l i = index (init l) i)
  = forall_intro (init_l_has_same_indices_except_last_implication l)

let rec reverse_stores_correct_values_base (#a:eqtype) (l:list a) (i:nat{i < length l})
  : Lemma (requires length l = length (reverse l))
          (ensures index l i = index (reverse l) (length l - 1 - i))
  = if i = 0 
    then (
      append_length (reverse (tail l)) [hd l];
      append_indices_from_second_list_are_stored_correctly_base (reverse (tail l)) [hd l] (length l - 1)
    )
    else (
      reverse_length_is_l_length (tail l);
      reverse_stores_correct_values_base (tail l) (i - 1);
      assert(reverse l = append (reverse (tail l)) [hd l]);
      last_from_append_is_init (reverse (tail l)) (hd l);
      assert(init (reverse l) = init (append (reverse (tail l)) [hd l]));
      assert(init (append (reverse (tail l)) [hd l]) = (reverse (tail l)));
      assert(length (tail l) - 1 - (i - 1) = length l - 1 - i);
      assert(reverse (tail l) = init (reverse l));
      init_l_has_same_indices_except_last (reverse l);
      assert(index (reverse l) (length l - 1 - i) = index (init (reverse l)) (length (tail l) - 1 - (i - 1)))
    )

let reverse_stores_correct_values_implication (#a:eqtype) (l:list a) (i:nat{i < length l})
  : Lemma (ensures length l = length (reverse l) ==> index l i = index (reverse l) (length l - 1 - i))
  = reverse_length_is_l_length l;
    move_requires (reverse_stores_correct_values_base l) i

let reverse_stores_correct_values (#a:eqtype) (l:list a)
  : Lemma (ensures forall (i:nat{i < length l}). length l = length (reverse l) ==> index l i = index (reverse l) (length l - 1 - i))
  = forall_intro (reverse_stores_correct_values_implication l)

let reverse_stores_correct_values_other (#a:eqtype) (l:list a)
  : Lemma (ensures forall (i:nat{i < length l}). length l = length (reverse l) ==> index l (length l - 1 - i) = index (reverse l) i)
  = reverse_stores_correct_values l

let gs : list int = create_gs pattern 0
 
let create_gs_length_is_l_length_for_gs ()
  : Lemma (ensures length gs = length pattern)
  = create_gs_length_is_l_length_base pattern

let create_gs_values_for_gs ()
  : Lemma (ensures forall (j:nat{j < length pattern}).
           length f = length pattern && length gs = length pattern ==>
           index gs j = index f (length pattern - 1) - (length pattern - j))
  = create_gs_values_forall_j pattern 0 

let r : (l:list english_letters{l <> []}) 
  = reverse pattern

let r_has_same_length_as_pattern ()
  : Lemma (ensures length r = length pattern)
  = reverse_length_is_l_length pattern

let r_has_correct_indices_stored ()
  : Lemma (ensures forall (i:nat{i < length pattern}). length pattern = length r ==> index pattern i = index r (length pattern - 1 - i))
  = reverse_stores_correct_values pattern

let g : (l:list int{l <> []}) 
    = create_pr r 1

let g_has_same_length_as_r ()
  : Lemma (ensures length g = length r)
  = create_pr_has_same_length_as_initial_list_base r

let create_pr_values_are_in_correct_index_for_g ()
  : Lemma (ensures forall (j:nat{j < length g}). index g j >= 0 && index g j < 1 + j)
  = create_pr_values_are_in_correct_index_forall_j r 1

let create_pr_gives_correct_result_for_g ()
  : Lemma (ensures forall (j:nat{j < length g}). length g = length r ==> 
          (let x = index g j in 
           x = maximum_frontier (first_characters r (1 + j)) (length (first_characters r (1 + j)))))
  = create_pr_gives_correct_result_forall_j r 1

let h : (l:list int{l <> []}) 
  = reverse g

let h_has_same_length_as_g ()
  : Lemma (ensures length h = length g)
  = reverse_length_is_l_length g 

let h_has_correct_indices_stored ()
  : Lemma (ensures forall (i:nat{i < length g}). length g = length h ==> index g i = index h (length g - 1 - i))
  = reverse_stores_correct_values g

let h_has_correct_indices_stored_other ()
  : Lemma (ensures forall (i:nat{i < length g}). length g = length h ==> index h i = index g (length g - 1 - i))
  = reverse_stores_correct_values_other g

// let first_characters_l_is_last_characters_reverse_l_base (l:list english_letters{l <> []}) (i:nat{i > 0 && i <= length l})
//   : Lemma (requires length l = length (reverse l))
//           (ensures first_characters l i = reverse (last_characters (reverse l) i))
//   = reverse_length_is_l_length l;
//     length_first_characters_i_is_i l i;
//     length_last_characters_i_is_i (reverse l) i;
//     reverse_length_is_l_length (last_characters (reverse l) i);
//     assert(length (last_characters (reverse l) i) = i);
//     assert(length (reverse (last_characters (reverse l) i)) = i);
//     assert(length (first_characters l i) = length (reverse (last_characters (reverse l) i)));
//     reverse_stores_correct_values l;
//     assert(forall (j:nat{j < length l}). index l j = index (reverse l) (length l - 1 - j));
//     first_characters_stores_indices_correctly l i;
//     assert(forall (j:nat{j < i}). index (first_characters l i) j = index l j);
//     assert(forall (j:nat{j < i}). index (first_characters l i) j = index (reverse l) (length l - 1 - j));
//     last_characters_stores_indices_correctly (reverse l) i;
//     assert(forall (j:nat{j < i}). index (last_characters (reverse l) i) j = index (reverse l) (length l - i + j));
//     reverse_stores_correct_values_other (last_characters (reverse l) i);
//     assert(forall (j:nat{j < i}). index (reverse (last_characters (reverse l) i)) j = index (last_characters (reverse l) i) (i - 1 - j));
//     compare_lists_equal_both_parts (first_characters l i) (reverse (last_characters (reverse l) i))

// let first_characters_l_is_last_characters_reverse_l_implication (l:list english_letters{l <> []}) (i:nat{i > 0 && i <= length l})
//   : Lemma (ensures length l = length (reverse l) ==> first_characters l i = reverse (last_characters (reverse l) i))
//   = reverse_length_is_l_length l;
//     move_requires (first_characters_l_is_last_characters_reverse_l_base l) i

// let first_characters_l_is_last_characters_reverse_l (l:list english_letters{l <> []}) 
//   : Lemma (ensures forall (i:nat{i > 0 && i <= length l}). 
//            length l = length (reverse l) ==> first_characters l i = reverse (last_characters (reverse l) i))
//   = forall_intro (first_characters_l_is_last_characters_reverse_l_implication l)



// let rec change_value (l:list int) (i:nat) (j:nat) (x:int) 
//   : list int 
//   = match l with
//     | [] -> []
//     | hd :: tl -> if i = j
//                   then x :: change_value tl (i + 1) j x 
//                   else hd :: change_value tl (i + 1) j x

let rec change_value (l:list int) (i:nat{i < length l}) (x:int)
  : list int 
  = match l with 
    | [] -> []
    | hd :: tl -> if i = 0 
                  then x :: tl 
                  else hd :: (change_value tl (i - 1) x)

let rec change_value_length_is_l_length_base (l:list int) (i:nat{i < length l}) (x:int) 
  : Lemma (ensures length (change_value l i x) = length l)
  = match l with 
    | [] -> ()
    | hd :: tl -> if i = 0 
                  then ()
                  else change_value_length_is_l_length_base tl (i - 1) x

let change_value_length_is_l_length (l:list int)
  : Lemma (ensures forall (i:nat{i < length l}) (x:int). length (change_value l i x) = length l)
  = forall_intro_2 (change_value_length_is_l_length_base l)

let rec change_value_has_correct_item_changed (l:list int) (i:nat{i < length l}) (x:int) 
  : Lemma (requires length l = length (change_value l i x))
          (ensures 
          (let l' = change_value l i x in 
           index l' i = x))
  = if i = 0 
    then ()
    else change_value_has_correct_item_changed (tail l) (i - 1) x

let rec change_value_has_the_same_items_base (l:list int) (i:nat{i < length l}) (x:int) 
                                             (j:nat{j < length l && j < length (change_value l i x) && j <> i})
  : Lemma (requires length l = length (change_value l i x))
          (ensures 
          (let l' = change_value l i x in 
           index l' j = index l j))
  = if i = 0 
    then ()
    else (
      if j = 0 
      then ()
      else change_value_has_the_same_items_base (tail l) (i - 1) x (j - 1)
    )

let change_value_has_the_same_items_implication (l:list int) (i:nat{i < length l}) (x:int) 
                                                (j:nat{j < length l && j < length (change_value l i x) && j <> i})
  : Lemma (ensures 
          (let l' = change_value l i x in 
           length l = length l' ==> index l' j = index l j))
  = move_requires (change_value_has_the_same_items_base l i x) j

let change_value_has_the_same_items (l:list int) (i:nat{i < length l}) (x:int) 
  : Lemma (ensures 
          (let l' = change_value l i x in forall (j:nat{j < length l && j < length (change_value l i x) && j <> i}).
           length l = length l' ==> index l' j = index l j))
  = forall_intro (change_value_has_the_same_items_implication l i x)

let change_value_has_correct_result (l:list int) (i:nat{i < length l}) (x:int) 
  : Lemma (requires length l = length (change_value l i x))
          (ensures 
          (let l' = change_value l i x in forall (j:nat{j < length l && j < length (change_value l i x) && j <> i}).
           index l' i = x && index l' j = index l j))
  = change_value_has_correct_item_changed l i x;
    change_value_has_the_same_items l i x

// val update_gs (gs:list int) (h:list int) (i:int{i >= 0}) (dim:nat) : Tot (list int) (decreases i)
// let rec update_gs gs h i dim =
//     match i with
//         | 0 -> gs
//         | _ -> update_gs (change_value gs (dim - (give_value h (dim - i) 0)) (dim - i) 0) h (i - 1) dim

// let rec update_gs (l:list int) (gs:list int{length gs = length l}) 
//                   (h:list int{length h = length l}) (i:nat{i <= length l})
//   : Tot (list int)
//     (decreases length l - i)
//   = 
//     if i = length l 
//     then gs
//     else let len = index h i in 
//          let gs' = change_value gs (length l - len) i in 
//          change_value_length_is_l_length gs;
//          update_gs l gs' h (i + 1)

// let final_gs : list int = append (update_gs gs h (length pattern) (length pattern)) ((length pattern) - 1)

// val give_value_letter (f:list english_letters) (nr:int) (i:nat{i >= 0}) : english_letters
// let rec give_value_letter f nr i =
//     match f with
//         | [] -> A
//         | hd::tl -> if i = nr
//                     then hd
//                     else give_value_letter tl nr (i + 1)
                    
// val boyer_moore (k:nat) (i:nat) (m:nat) (n:nat) (t:list english_letters) (p:list english_letters) (bc:list int) (gs:list int) (alphabet:list english_letters) : Tot bool (decreases %[i;k])
// let rec boyer_moore k i m n t p bc gs alphabet =
//     match k, i with 
//         | _, 0 -> false
//         | 0, _ -> true
//         | _, _ -> if give_value_letter t ((n - m + 1 - i) + m - 1 - (m - k)) 0 <> give_value_letter p (m - 1 - (m - k)) 0
//                   then let shiftbc = m - (m - k) - 1 - (give_value bc (alphabet_character_index (give_value_letter t ((n - m + 1 - i) + m - 1 - (m - k)) 0) alphabet 0) 0) in
//                        let shiftgs = m - (m - k) - (give_value gs (m - (m - k)) 0) in
//                        let index = i - (maximum shiftbc shiftgs) in
//                        if index >= 0 && index < i
//                        then boyer_moore m index m n t p bc gs alphabet
//                        else boyer_moore m 0 m n t p bc gs alphabet
//                   else boyer_moore (k - 1) i m n t p bc gs alphabet

//conversion functions, print and main
// let rec belongs (t:list english_letters) (p:list english_letters{length p <= length t}) (i:nat)
//   : bool 
//   = match p with
//     | [] -> true
//     | hd :: tl -> if i < length t && hd = index t i 
//                   then belongs t tl (i + 1)
//                   else false

let convert_to_int f =
  match f with
    | false -> 0
    | true -> 1

let string_of_int_list l =
  Printf.sprintf "[%s]" (String.concat "; " (List.Tot.map (Printf.sprintf "%d") l))

let convert_character_to_int (c:english_letters) 
  = match c with 
    | A -> 1 
    | B -> 2 
    | _ -> -1
    // | C -> 3
    // | D -> 4
    // | E -> 5
    // | F -> 6
    // | G -> 7
    // | H -> 8
    // | I -> 9
    // | J -> 10
    // | K -> 11
    // | L -> 12
    // | M -> 13
    // | M -> 14
    // | O -> 15
    // | P -> 16
    // | Q -> 17
    // | R -> 18
    // | S -> 19
    // | T -> 20
    // | U -> 21
    // | V -> 22
    // | W -> 23
    // | X -> 24
    // | Y -> 25
    // | Z -> 26
    // | _ -> -1

let rec convert_letters_to_int (l:list english_letters) : list int =
  match l with
    | [] -> []
    | hd :: tl -> (convert_character_to_int hd) :: (convert_letters_to_int tl)

// let convert_letter_to_int c =
//   alphabet_character_index c alphabet 0

let main() =
  let message =
     sprintf "The result is %s\n" (string_of_int_list (append [1;2;3;4;9] [5;1;2]))
  in
  print_string message

#push-options "--warn_error -272"
let _ = main()
#pop-options