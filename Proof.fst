module Proof

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
let text = [A;B;B;A;X;A;B;X;A;A;X;B;A;X;B;A;A;A;B;A;B;B]

val pattern : list english_letters
let pattern = [B;A;X;A;B]

val alphabet_length : (i:nat{i > 0})
let alphabet_length = length alphabet

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

// let mem_index_range_index_is_item (#a:eqtype) (l:list a)
//   : Lemma (requires length l <= 4) //from 8 it doesn't work
//           (ensures forall (item:a).
//           (let i = item_index item l (length l) in
//            i <> -1 && i < length l ==> index l i = item))
//   = ()

// let item_not_found_returns_minusone_specific_element (#a:eqtype) (l:list a)
//   : Lemma (requires length l <= 6) //from 7 it doesn't work
//           (ensures forall (item:a). item_index item l (length l) = -1 ==> (forall (i:nat{i < length l}). index l i <> item))
//   = ()

// let one_index_not_item (#a:eqtype) (item:a) (l:list a) (i:nat{i < length l})
//   : Type
//   = index l i <> item

// let item_not_found_returns_minusone_one_index (#a:eqtype) (item:a) (l:list a) (i:nat{i < length l})
//   : Lemma (requires item_index item l (length l) = -1)
//           (ensures one_index_not_item item l ((length l) - 1))
//   = ()

// let rec item_not_found_item_not_found_less_indexes (#a:eqtype) (l:list a)
//   : Lemma (ensures forall (item:a). item_index item l (length l) = -1 ==> (forall (i:nat{i < length l}). item_index item l i = -1))
//   = match l with
//     | [] -> ()
//     | hd :: tl -> item_not_found_item_not_found_less_indexes tl

// let rec item_not_found_returns_minusone (#a:eqtype) (l:list a)
//   : Lemma (ensures forall (item:a). item_index item l (length l) = -1 ==> (forall (i:nat{i < length l}). one_index_not_item i))
//   = match l with
//     | [] -> ()
//     | hd :: tl -> admit(item_not_found_returns_minusone tl);
//                   item_not_found_returns_minusone_one_index l

// let item_found_returns_nat (#a:eqtype) (l:list a)
//   : Lemma (ensures forall (item:a). 
//           (let i = item_index item l (length l) in
//            i <> -1 ==> i >= 0))
//   = ()

// let rec item_found_returns_index (#a:eqtype) (l:list a)
//   : Lemma (ensures forall (item:a). 
//           (let i = item_index item l (length l) in
//            i <> -1 && i < length l ==> index l i = item))
//   = match l with
//     | [] -> ()
//     | hd :: tl -> item_found_returns_index tl

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

// val last_characters (l:list english_letters) (dim:nat) (i:nat) (j:nat{j >= 0}) : list english_letters
// let rec last_characters l dim i j =
//     match l with
//         | [] -> []
//         | hd::tl -> if i >= dim - j
//                     then hd :: last_characters tl dim (i + 1) j
//                     else last_characters tl dim (i + 1) j

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

let rec last_characters_stores_indices_correctly_base (l:list english_letters) (i:nat{i <= length l}) (j:nat{j < i && j < length (last_characters l i)})
  : Lemma (ensures 
           (let l' = last_characters l i in 
            index l' j = index l ((length l) - i)))
  = match l with 
    | [] -> ()
    | hd :: tl -> match j with 
                  | 0 -> ()
                  | _ -> assert(last_characters l i = (index l ((length l) - i)) :: (last_characters tl (i - 1)));
                         assert(index (last_characters l i) j = index (last_characters tl (i - 1)) (j - 1));
                         last_characters_stores_indices_correctly_base tl (i - 1) (j - 1);
                         assert(index (last_characters tl (i - 1)) (j - 1) = index tl ((length tl) - (i - 1)));
                         assert(length tl = (length l) - 1);
                         assert(index (last_characters tl (i - 1)) (j - 1) = index tl ((length l) - i));
                         admit()

val compare_frontier (l:list english_letters) (i:nat{i <= length l}) : bool
let compare_frontier l i =
    if first_characters l i = last_characters l i && i < (length l)
    then true
    else false
    
let rec compare_lists_base (l1:list english_letters) (l2:list english_letters) (i:nat{i < length l1 && i < length l2})
  : Lemma (ensures l1 = l2 ==> (length l1 = length l2) /\ (index l1 i = index l2 i))
  = match l1 with 
    | [] -> ()
    | hd1 :: tl1 -> match l2 with 
                    | [] -> ()
                    | hd2 :: tl2 -> match i with 
                                    | 0 -> ()
                                    | _ -> compare_lists_base tl1 tl2 (i - 1) 

let compare_lists (l1:list english_letters) (l2:list english_letters)
  : Lemma (ensures forall (i:nat{i < length l1 && i < length l2}). l1 = l2 ==> (length l1 = length l2) && (index l1 i = index l2 i))
  = forall_intro (compare_lists_base l1 l2)

let compare_frontier_true_i_less_than_length_l (l:list english_letters) (i:nat{i <= length l})
  : Lemma (ensures compare_frontier l i ==> i < length l)
  = ()

let not_equal_unequal (l1:list english_letters) (l2:list english_letters)
  : Lemma (ensures ~(l1 = l2) ==> l1 <> l2)
  = ()

let not_length_equal_length_unequal (l1:list english_letters) (l2:list english_letters)
  : Lemma (ensures ~(length l1 = length l2) ==> length l1 <> length l2)
  = ()

let negation_forall_indices_is_exists_index (l1:list english_letters) (l2:list english_letters) 
  : Lemma (ensures ~(forall (i:nat{i < length l1 && i < length l2}). index l1 i = index l2 i) ==> (exists (i:nat{i < length l1 && i < length l2}). index l1 i <> index l2 i))
  = ()

let compare_lists_false_base (l1:list english_letters) (l2:list english_letters) 
  : Lemma (ensures ~(l1 = l2) ==> ~((length l1 = length l2) /\ (forall (i:nat{i < length l1 && i < length l2}). index l1 i = index l2 i)))
  = compare_lists l1 l2;
    not_equal_unequal l1 l2;
    not_length_equal_length_unequal l1 l2;
    negation_forall_indices_is_exists_index l1 l2;
    admit()

let compare_lists_false (l1:list english_letters) (l2:list english_letters) 
  : Lemma (ensures l1 <> l2 ==> (length l1 <> length l2) /\ (exists (i:nat{i < length l1 && i < length l2}). index l1 i <> index l2 i))
  = admit()

let compare_frontier_true_first_characters_are_equal_with_last_characters (l:list english_letters) (i:nat{i <= length l})
  : Lemma (ensures compare_frontier l i = true ==> first_characters l i = last_characters l i)
  = ()

let compare_first_characters_with_last_characters (l:list english_letters) (i:nat{i <= length l})
  : Lemma (ensures forall (j:nat{j < length (first_characters l i) && j < length (last_characters l i)}).
           (let l1 = first_characters l i in
            let l2 = last_characters l i in 
            l1 = l2 ==> (length l1 = length l2) && (index l1 j = index l2 j)))
  = compare_lists (first_characters l i) (last_characters l i)

let compare_frontiers_true_gives_correct_result (l:list english_letters) (i:nat{i <= length l})
  : Lemma (ensures forall (j:nat{j < length (first_characters l i) && j < length (last_characters l i)}). 
           (let l1 = first_characters l i in
            let l2 = last_characters l i in 
            compare_frontier l i = true ==> (length l1 = length l2) && (index l1 j = index l2 j) && i < length l))
  = compare_frontier_true_i_less_than_length_l l i;
    compare_frontier_true_first_characters_are_equal_with_last_characters l i;
    compare_first_characters_with_last_characters l i

// val maximum (m:int) (n:int) : int
// let maximum m n =
//     if m > n 
//     then m
//     else n

// val maximum_frontier (l:list english_letters) (dim:nat) (i:nat) (j:nat{j <= length l}) : nat
// let rec maximum_frontier l dim i j =
//     match j with
//         | 0 -> 0
//         | _ -> if compare_frontier l dim i j = true
//                then j
//                else maximum_frontier l dim i (j - 1)

// val append (#a:Type) (m:list a) (n:a) : list a
// let rec append m n = 
//     match m with
//         | [] -> n :: []
//         | hd :: tl -> hd :: (append tl n)

// val reverse (#a:Type) (l:list a) : list a
// let rec reverse l =
//     match l with
//         | [] -> []
//         | hd :: tl -> append (reverse tl) hd

// val create_pr (l:list english_letters) (j:nat{j <= length l}) : list int
// let rec create_pr l j =
//     match j with 
//         | 0 -> [-1]
//         | _ -> (maximum_frontier (first_characters l j) (length (first_characters l j)) 0 (length (first_characters l j))) :: (create_pr l (j - 1))
               
// let f : list int = reverse (create_pr pattern (length pattern))

// val give_value (f:list int) (nr:int) (i:nat{i >= 0}) : int
// let rec give_value f nr i =
//     match f with
//         | [] -> -1
//         | hd::tl -> if i = nr
//                     then hd
//                     else give_value tl nr (i + 1)

// val create_gs (f:list int) (m:nat) (i:nat{i >= 0}) : list int
// let rec create_gs f m i =
//     match i with
//         | 0 -> [(give_value f m 0) - m]
//         | _ -> ((give_value f m 0) - m + i) :: (create_gs f m (i - 1))
        
// let gs : list int = reverse (create_gs f (length pattern) ((length pattern) - 1))
 
// let r : list english_letters = reverse pattern
// let g : list int = reverse (create_pr r (length r)) 
// let h : list int = reverse g

// val change_value (l:list int) (m:int) (n:int) (i:nat{i >= 0}) : list int
// let rec change_value l m n i : Tot (list int) (decreases l) =
//     match l with
//         | [] -> []
//         | hd :: tl -> if i = m
//                       then n :: change_value tl m n (i + 1)
//                       else hd :: change_value tl m n (i + 1)
                      
// val update_gs (gs:list int) (h:list int) (i:int{i >= 0}) (dim:nat) : Tot (list int) (decreases i)
// let rec update_gs gs h i dim =
//     match i with
//         | 0 -> gs
//         | _ -> update_gs (change_value gs (dim - (give_value h (dim - i) 0)) (dim - i) 0) h (i - 1) dim

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
let rec belongs (t:list english_letters) (p:list english_letters{length p < length t}) (i:nat{i <= length t - length p})
  : bool 
  = match p with
    | [] -> true
    | hd :: tl -> if hd = index t i 
                  then belongs t tl (i + 1)
                  else false

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
    | C -> 3
    | D -> 4
    | E -> 5
    | F -> 6
    | G -> 7
    | H -> 8
    | I -> 9
    | J -> 10
    | K -> 11
    | L -> 12
    | M -> 13
    | M -> 14
    | O -> 15
    | P -> 16
    | Q -> 17
    | R -> 18
    | S -> 19
    | T -> 20
    | U -> 21
    | V -> 22
    | W -> 23
    | X -> 24
    | Y -> 25
    | Z -> 26
    | _ -> -1

let rec convert_letters_to_int (l:list english_letters) : list int =
  match l with
    | [] -> []
    | hd :: tl -> (convert_character_to_int hd) :: (convert_letters_to_int tl)

// let convert_letter_to_int c =
//   alphabet_character_index c alphabet 0

let main() =
  let message =
     sprintf "The result is %d\n" (convert_to_int (belongs text pattern 2))
  in
  print_string message

#push-options "--warn_error -272"
let _ = main()
#pop-options