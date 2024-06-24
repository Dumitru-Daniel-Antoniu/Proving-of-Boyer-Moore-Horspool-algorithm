module BoyerMooreHorspool

open Belongs
open UpdateBc
open GlobalData
open ItemIndices
open NewOrOld
open FStar.Classical 
open FStar.IO
open FStar.Printf
open FStar.List
open FStar.List.Tot.Base

let rec boyer_moore_horspool (t:list english_letters) (p:list english_letters{length p <= length t}) (k:nat{k <= length p}) (i:nat) 
  : Tot (result:int{result >= -1}) 
  (decreases %[(if i < length t - length p + 1 then length t - length p + 1 - i else 0); length p - k]) 
  = let m = length p in
    let n = length t in
    if k = m then i
    else if i > n - m then -1 
    else (
      if index t (i + m - 1 - k) = index p (m - 1 - k)
      then boyer_moore_horspool t p (k + 1) i
      else (
        update_bc_length_is_initial_list_length alphabet p;
        mem_last_list (item_indices (index t (i + m - 1 - k)) alphabet 0);
        item_indices_is_in_interval_forall alphabet 0 (index t (i + m - 1 - k));
        let shiftbc = m - k - 1 - index (update_bc alphabet p) (last (item_indices (index t (i + m - 1 - k)) alphabet 0)) in
        let value = i + (maximum 1 shiftbc) in
        boyer_moore_horspool t p 0 value
      ) 
    )

let bmh_result_base (t:list english_letters) (p:list english_letters{length p <= length t}) 
                            (k:nat{k < length p}) (i:nat{i <= length t - length p})
  : Lemma (requires boyer_moore_horspool t p k i = boyer_moore_horspool t p (length p) i)
          (ensures boyer_moore_horspool t p k i = i)
  = ()

let bmh_result_implication (t:list english_letters) (p:list english_letters{length p <= length t}) 
                                   (k:nat{k < length p}) (i:nat{i <= length t - length p})
  : Lemma (ensures boyer_moore_horspool t p k i = boyer_moore_horspool t p (length p) i ==> boyer_moore_horspool t p k i = i)
  = move_requires (bmh_result_base t p k) i

let bmh_result (t:list english_letters) (p:list english_letters{length p <= length t})
  : Lemma (ensures forall (k:nat{k < length p}) (i:nat{i <= length t - length p}). boyer_moore_horspool t p k i = boyer_moore_horspool t p (length p) i ==> boyer_moore_horspool t p k i = i)
  = forall_intro_2 (bmh_result_implication t p)

let rec bmh_value_comparison (t:list english_letters) (p:list english_letters{length p <= length t}) 
                                     (k:nat{k <= length p}) (i:nat)
  : Lemma (ensures boyer_moore_horspool t p k i <> boyer_moore_horspool t p (length p) i ==> boyer_moore_horspool t p k i > i || boyer_moore_horspool t p k i = -1)
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
        then bmh_value_comparison t p (k + 1) i
        else (
          update_bc_length_is_initial_list_length alphabet p;
          mem_last_list (item_indices (index t (i + length p - 1 - k)) alphabet 0);
          item_indices_is_in_interval_forall alphabet 0 (index t (i + length p - 1 - k));
          let shiftbc = m - k - 1 - index (update_bc alphabet p) (last (item_indices (index t (i + m - 1 - k)) alphabet 0)) in
          let value = i + (maximum 1 shiftbc) in
          bmh_value_comparison t p 0 value
        )
      )
    )

let k_to_m_then_index_is_equal (t:list english_letters) (p:list english_letters{length p <= length t}) 
                                   (k:nat{k < length p}) (i:nat{i <= length t - length p})
  : Lemma (requires boyer_moore_horspool t p k i = boyer_moore_horspool t p (length p) i)
          (ensures index t (i + length p - 1 - k) = index p (length p - 1 - k))
  = update_bc_length_is_initial_list_length alphabet p;
    mem_last_list (item_indices (index t (i + length p - 1 - k)) alphabet 0);
    item_indices_is_in_interval_forall alphabet 0 (index t (i + length p - 1 - k));
    let bc = update_bc alphabet p in
    let shiftbc = length p - k - 1 - index bc (last (item_indices (index t (i + length p - 1 - k)) alphabet 0)) in
    let value = i + (maximum 1 shiftbc) in
    if index t (i + length p - 1 - k) <> index p (length p - 1 - k)
    then (
      assert(index t (i + length p - 1 - k) <> index p (length p - 1 - k) ==> boyer_moore_horspool t p k i = boyer_moore_horspool t p 0 value);
      bmh_value_comparison t p 0 value;
      assert(boyer_moore_horspool t p 0 value > i || boyer_moore_horspool t p 0 value = -1);
      assert(boyer_moore_horspool t p 0 value <> boyer_moore_horspool t p (length p) i)
    )
    else ()

let rec k_to_m_then_k'_index_is_equal_base (t:list english_letters) (p:list english_letters{length p <= length t}) 
                                      (k:nat{k < length p}) (i:nat{i <= length t - length p})
                                      (k':nat{k' >= k && k' < length p})
  : Lemma (requires boyer_moore_horspool t p k i = boyer_moore_horspool t p (length p) i)
          (ensures index t (i + length p - 1 - k') = index p (length p - 1 - k'))
          (decreases length p - k)
  = k_to_m_then_index_is_equal t p k i;
    if k = length p - 1
    then ()
    else if k = k' then ()
    else (
      assert(index t (i + length p - 1 - k) = index p (length p - 1 - k) ==> boyer_moore_horspool t p k i = boyer_moore_horspool t p (k + 1) i);
      k_to_m_then_k'_index_is_equal_base t p (k + 1) i k'
    )

let k_to_m_then_k'_index_is_equal_implication (t:list english_letters) (p:list english_letters{length p <= length t}) 
                                              (k:nat{k < length p}) (i:nat{i <= length t - length p})
                                              (k':nat{k' >= k && k' < length p})
  : Lemma (ensures boyer_moore_horspool t p k i = boyer_moore_horspool t p (length p) i ==> index t (i + length p - 1 - k') = index p (length p - 1 - k'))
  = move_requires (k_to_m_then_k'_index_is_equal_base t p k i) k'

let k_to_m_then_k'_index_is_equal_forall_k' (t:list english_letters) (p:list english_letters{length p <= length t}) 
                                            (k:nat{k < length p}) (i:nat{i <= length t - length p})
  : Lemma (ensures boyer_moore_horspool t p k i = boyer_moore_horspool t p (length p) i ==> 
           (forall (k':nat{k' >= k && k' < length p}). index t (i + length p - 1 - k') = index p (length p - 1 - k')))
  = forall_intro (k_to_m_then_k'_index_is_equal_implication t p k i)

let k_to_m_then_k'_index_is_equal (t:list english_letters) (p:list english_letters{length p <= length t}) 
  : Lemma (ensures forall (k:nat{k < length p}) (i:nat{i <= length t - length p}). 
           boyer_moore_horspool t p k i = boyer_moore_horspool t p (length p) i ==> 
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
  : Lemma (requires boyer_moore_horspool t p 0 i = boyer_moore_horspool t p (length p) i)
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

let zero_to_k_then_all_indices_are_equal (t:list english_letters) (p:list english_letters{length p <= length t}) 
                                         (k:nat{k < length p}) (i:nat{i <= length t - length p})
  : Lemma (requires (forall (k':nat{k' < k}). index t (i + length p - 1 - k') = index p (length p - 1 - k')) /\
                    index t (i + length p - 1 - k) = index p (length p - 1 - k))
          (ensures boyer_moore_horspool t p k i = boyer_moore_horspool t p (k + 1) i /\
                   (forall (k':nat{k' < k + 1}). index t (i + length p - 1 - k') = index p (length p - 1 - k')))
  = ()

let rec bmh_not_equal_indices_then_increase_i (t:list english_letters) (p:list english_letters{length p <= length t}) 
                                                      (k:nat{k < length p}) (i:nat{i <= length t - length p})
  : Lemma (requires boyer_moore_horspool t p k i <> boyer_moore_horspool t p (length p) i)
          (ensures exists (k':nat{k' >= k && k' < length p}). index t (i + length p - 1 - k') <> index p (length p - 1 - k'))
          (decreases length p - k)
  = if index t (i + length p - 1 - k) = index p (length p - 1 - k)
    then bmh_not_equal_indices_then_increase_i t p (k + 1) i 
    else ()

let from_zero_to_i_bmh_does_not_return_i_base (t:list english_letters) (p:list english_letters{length p <= length t}) 
                                                      (i:nat{i <= length t - length p}) (i':nat{i' < i})
  : Lemma (requires forall (j:nat{j < i}). boyer_moore_horspool t p 0 j <> j)
          (ensures boyer_moore_horspool t p 0 i' <> boyer_moore_horspool t p (length p) i')
  = ()

let from_zero_to_i_bmh_does_not_return_i_implication (t:list english_letters) (p:list english_letters{length p <= length t}) 
                                                             (i:nat{i <= length t - length p}) (i':nat{i' < i})
  : Lemma (ensures (forall (j:nat{j < i}). boyer_moore_horspool t p 0 j <> j) ==> boyer_moore_horspool t p 0 i' <> boyer_moore_horspool t p (length p) i')
  = move_requires (from_zero_to_i_bmh_does_not_return_i_base t p i) i'

let from_zero_to_i_bmh_does_not_return_i (t:list english_letters) (p:list english_letters{length p <= length t}) 
                                                 (i:nat{i <= length t - length p}) 
  : Lemma (ensures forall (i':nat{i' < i}). (forall (j:nat{j < i}). boyer_moore_horspool t p 0 j <> j) ==> boyer_moore_horspool t p 0 i' <> boyer_moore_horspool t p (length p) i')
  = forall_intro (from_zero_to_i_bmh_does_not_return_i_implication t p i)

let from_zero_to_i_belongs_is_false_base (t:list english_letters) (p:list english_letters{length p <= length t}) 
                                         (i:nat{i <= length t - length p}) (i':nat{i' < i})
  : Lemma (requires forall (j:nat{j < i}). boyer_moore_horspool t p 0 j <> j)
          (ensures belongs t p i' = false)
  = from_zero_to_i_bmh_does_not_return_i t p i;
    bmh_not_equal_indices_then_increase_i t p 0 i';
    index_is_not_equal_belongs_false_base t p i'

let from_zero_to_i_belongs_is_false_implication (t:list english_letters) (p:list english_letters{length p <= length t}) 
                                                (i:nat{i <= length t - length p}) (i':nat{i' < i})
  : Lemma (ensures (forall (j:nat{j < i}). boyer_moore_horspool t p 0 j <> j) ==> belongs t p i' = false)
  = move_requires (from_zero_to_i_belongs_is_false_base t p i) i'

let from_zero_to_i_belongs_is_false (t:list english_letters) (p:list english_letters{length p <= length t}) 
                                    (i:nat{i <= length t - length p})
  : Lemma (ensures forall (i':nat{i' < i}). (forall (j:nat{j < i}). boyer_moore_horspool t p 0 j <> j) ==> belongs t p i' = false)
  = forall_intro (from_zero_to_i_belongs_is_false_implication t p i)

let bmh_to_value_then_not_bmh_to_length_p (t:list english_letters) (p:list english_letters{length p <= length t}) 
                                                          (k:nat{k < length p}) (i:nat{i <= length t - length p}) 
  : Lemma (requires item_indices (index t (i + length p - 1 - k)) alphabet 0 <> [] /\
           last (item_indices (index t (i + length p - 1 - k)) alphabet 0) < length (update_bc alphabet p) /\
          (let bc = update_bc alphabet p in
           let shiftbc = length p - k - 1 - index bc (last (item_indices (index t (i + length p - 1 - k)) alphabet 0)) in
           let value = i + (maximum 1 shiftbc) in
           (forall (k':nat{k' < k}). index t (i + length p - 1 - k') = index p (length p - 1 - k')) /\
           index t (i + length p - 1 - k) <> index p (length p - 1 - k)))
          (ensures boyer_moore_horspool t p k i <> boyer_moore_horspool t p (length p) i)
  = assert(boyer_moore_horspool t p (length p) i = i);
    let bc = update_bc alphabet p in
    let shiftbc = length p - k - 1 - index bc (last (item_indices (index t (i + length p - 1 - k)) alphabet 0)) in
    let value = i + (maximum 1 shiftbc) in
    update_bc_length_is_initial_list_length alphabet p;
    assert(length bc = length alphabet);
    bmh_value_comparison t p 0 value

let number_is_in_interval (i:nat) (i':nat{i' >= i && i' < i + 1})
  : Lemma (ensures i' = i)
  = ()

#push-options "--split_queries always"
let bmh_belongs_false_if_less_than_shiftbc (t:list english_letters) (p:list english_letters{length p <= length t}) 
                                           (k:nat{k < length p}) (i:nat{i <= length t - length p}) 
                                           (i':nat{i' >= i})
  : Lemma (requires item_indices (index t (i + length p - 1 - k)) alphabet 0 <> [] /\
           last (item_indices (index t (i + length p - 1 - k)) alphabet 0) < length (update_bc alphabet p) /\
          (let bc = update_bc alphabet p in
           let shiftbc = length p - k - 1 - index bc (last (item_indices (index t (i + length p - 1 - k)) alphabet 0)) in
           let value = i + (maximum 1 shiftbc) in
           (forall (j:nat{j < i}). belongs t p j = false) /\
           (forall (k':nat{k' < k}). index t (i + length p - 1 - k') = index p (length p - 1 - k')) /\
           index t (i + length p - 1 - k) <> index p (length p - 1 - k) /\ i' < minimum value (length t - length p + 1)))
          (ensures belongs t p i' = false)
          (decreases length p - k)
  = let bc = update_bc alphabet p in
    let shiftbc = length p - k - 1 - index bc (last (item_indices (index t (i + length p - 1 - k)) alphabet 0)) in
    let value = i + (maximum 1 shiftbc) in
    assert(forall (k':nat{k' < k}). index t (i + length p - 1 - k') = index p (length p - 1 - k'));
    assert(index t (i + length p - 1 - k) <> index p (length p - 1 - k));
    bmh_to_value_then_not_bmh_to_length_p t p k i;
    assert(boyer_moore_horspool t p k i <> boyer_moore_horspool t p (length p) i);
    assert(boyer_moore_horspool t p k i = boyer_moore_horspool t p 0 value);
    if shiftbc > 0
    then (
      assert(index bc (last (item_indices (index t (i + length p - 1 - k)) alphabet 0)) < length p - 1 - k);
      assert(i + length p - 1 - k >= 0 && i + length p - 1 - k < length t);
      update_bc_length_is_initial_list_length alphabet p;
      update_bc_has_values_in_interval alphabet p (last (item_indices (index t (i + length p - 1 - k)) alphabet 0));
      assert(index bc (last (item_indices (index t (i + length p - 1 - k)) alphabet 0)) = -1 || 
            (index bc (last (item_indices (index t (i + length p - 1 - k)) alphabet 0)) >= 0 &&
              index bc (last (item_indices (index t (i + length p - 1 - k)) alphabet 0)) < length p));

      let a = last (item_indices (index t (i + length p - 1 - k)) alphabet 0) in 
      let b = index bc (last (item_indices (index t (i + length p - 1 - k)) alphabet 0)) in
        
      if b = -1 
      then (
        update_bc_for_minusone_forall_j alphabet p a;
        assert(forall (j:nat{j < length p}). index p j <> index alphabet a);

        mem_last_list (item_indices (index t (i + length p - 1 - k)) alphabet 0);
        assert(mem a (item_indices (index t (i + length p - 1 - k)) alphabet 0) = true);
          
        index_is_mem_is_item_base alphabet (index t (i + length p - 1 - k)) a;
        assert(index alphabet a = index t (i + length p - 1 - k));
        assert(forall (z:nat{z < length p}). index p z <> index t (i + length p - 1 - k))
      )
      else (
        update_bc_for_nat_base alphabet p a b;
        assert(index bc a = b);
        assert(index p b = index alphabet a);
        assert(forall (c:nat{c > b && c < length p}). index p c <> index alphabet a);

        mem_last_list (item_indices (index t (i + length p - 1 - k)) alphabet 0);
        assert(mem a (item_indices (index t (i + length p - 1 - k)) alphabet 0) = true);
          
        index_is_mem_is_item_base alphabet (index t (i + length p - 1 - k)) a;
        assert(index alphabet a = index t (i + length p - 1 - k));
        assert(forall (d:nat{d > b && d < length p}). index p d <> index t (i + length p - 1 - k));

        assert(shiftbc = maximum 1 shiftbc);
        assert(index t (i + length p - 1 - k) <> index p (length p - 1 - k));
          
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
      assert(index t (i' + length p - 1 - k) <> index p (length p - 1 - k))
    );
    index_is_not_equal_belongs_false_base t p i';
    assert((exists (y:nat{y >= i' && y < i' + length p}). index t y <> index p (y - i')) ==> belongs t p i' = false);
    assert(i + length p - 1 - k >= i')
#pop-options

let bmh_belongs_false_if_less_than_shiftbc_implication (t:list english_letters) (p:list english_letters{length p <= length t}) 
                                                               (k:nat{k < length p}) (i:nat{i <= length t - length p}) 
                                                               (i':nat{i' >= i})
  : Lemma (ensures (item_indices (index t (i + length p - 1 - k)) alphabet 0 <> [] /\
           last (item_indices (index t (i + length p - 1 - k)) alphabet 0) < length (update_bc alphabet p) /\
          (let bc = update_bc alphabet p in
           let shiftbc = length p - k - 1 - index bc (last (item_indices (index t (i + length p - 1 - k)) alphabet 0)) in
           let value = i + (maximum 1 shiftbc) in
           (forall (j:nat{j < i}). belongs t p j = false) /\
           (forall (k':nat{k' < k}). index t (i + length p - 1 - k') = index p (length p - 1 - k')) /\
           index t (i + length p - 1 - k) <> index p (length p - 1 - k) /\ i' < minimum value (length t - length p + 1)))
           ==> belongs t p i' = false)
  = move_requires (bmh_belongs_false_if_less_than_shiftbc t p k i) i'

let bmh_belongs_false_if_less_than_shiftbc_forall (t:list english_letters) (p:list english_letters{length p <= length t}) 
                                                          (k:nat{k < length p}) (i:nat{i <= length t - length p}) 
  : Lemma (ensures forall (i':nat{i' >= i}). (item_indices (index t (i + length p - 1 - k)) alphabet 0 <> [] /\
           last (item_indices (index t (i + length p - 1 - k)) alphabet 0) < length (update_bc alphabet p) /\
          (let bc = update_bc alphabet p in
           let shiftbc = length p - k - 1 - index bc (last (item_indices (index t (i + length p - 1 - k)) alphabet 0)) in
           let value = i + (maximum 1 shiftbc) in
           (forall (j:nat{j < i}). belongs t p j = false) /\
           (forall (k':nat{k' < k}). index t (i + length p - 1 - k') = index p (length p - 1 - k')) /\
           index t (i + length p - 1 - k) <> index p (length p - 1 - k) /\ i' < minimum value (length t - length p + 1)))
           ==> belongs t p i' = false)
  = forall_intro (bmh_belongs_false_if_less_than_shiftbc_implication t p k i)

let forall_true_and_for_k_true_then_forall_plus_one_true (t:list english_letters) (p:list english_letters{length p <= length t})
                                                         (k:nat{k < length p}) (i:nat{i <= length t - length p})
  : Lemma (requires (forall (k':nat{k' < k}). index t (i + length p - 1 - k') = index p (length p - 1 - k')) /\
                     index t (i + length p - 1 - k) = index p (length p - 1 - k))
          (ensures forall (k':nat{k' < k + 1}). index t (i + length p - 1 - k') = index p (length p - 1 - k'))
  = ()

let rec bmh_gives_correct_result (t:list english_letters) (p:list english_letters{length p <= length t})
                                         (k:nat{k <= length p}) (i:nat{i <= length t - length p})
  : Lemma (requires  
           (forall (i':nat{i' < i}). belongs t p i' = false) /\ 
           (forall (k':nat{k' < k}). index t (i + length p - 1 - k') = index p (length p - 1 - k')))
          (ensures 
          (let x = boyer_moore_horspool t p k i in 
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
        zero_to_k_then_all_indices_are_equal t p k i;
        bmh_gives_correct_result t p (k + 1) i 
      )
      else (
        update_bc_length_is_initial_list_length alphabet p;
        mem_last_list (item_indices (index t (i + length p - 1 - k)) alphabet 0);
        item_indices_is_in_interval_forall alphabet 0 (index t (i + length p - 1 - k));
        let shiftbc = length p - k - 1 - index (update_bc alphabet p) (last (item_indices (index t (i + length p - 1 - k)) alphabet 0)) in
        let value = i + (maximum 1 shiftbc) in
        if value > length t - length p
        then ()
        else (
          bmh_belongs_false_if_less_than_shiftbc_forall t p k i;
          bmh_gives_correct_result t p 0 value
        )
      )
    )

let bmh_gives_correct_result_for_text_and_pattern ()
  : Lemma (ensures 
          (let x = boyer_moore_horspool text pattern 0 0 in 
           x <> -1 ==> belongs text pattern x = true))
  = assert(0 <= length text - length pattern);
    bmh_gives_correct_result text pattern 0 0

let rec bmh_gives_minus_one_belongs_false (t:list english_letters) (p:list english_letters{length p <= length t})
                                                  (k:nat{k <= length p}) (i:nat{i <= length t - length p})
  : Lemma (requires  
           (forall (i':nat{i' < i}). belongs t p i' = false) /\ 
           (forall (k':nat{k' < k}). index t (i + length p - 1 - k') = index p (length p - 1 - k')))
          (ensures 
          (let x = boyer_moore_horspool t p k i in 
           x = -1 ==> (forall (y:nat{y <= length t - length p}). belongs t p y = false)))
          (decreases %[(if i < length t - length p + 1 then length t - length p + 1 - i else 0); length p - k])
  = if k = length p 
    then ()
    else (
      assert(k < length p);
      if index t (i + length p - 1 - k) = index p (length p - 1 - k)
      then (
        zero_to_k_then_all_indices_are_equal t p k i;
        bmh_gives_minus_one_belongs_false t p (k + 1) i
      )
      else (
        update_bc_length_is_initial_list_length alphabet p;
        mem_last_list (item_indices (index t (i + length p - 1 - k)) alphabet 0);
        item_indices_is_in_interval_forall alphabet 0 (index t (i + length p - 1 - k));
        let shiftbc = length p - k - 1 - index (update_bc alphabet p) (last (item_indices (index t (i + length p - 1 - k)) alphabet 0)) in
        let value = i + (maximum 1 shiftbc) in
        bmh_belongs_false_if_less_than_shiftbc_forall t p k i; 
        if value > length t - length p 
        then ()
        else bmh_gives_minus_one_belongs_false t p 0 value
      )
    )

let bmh_gives_minus_one_belongs_false_for_text_and_pattern ()
  : Lemma (ensures 
          (let x = boyer_moore_horspool text pattern 0 0 in 
           x = -1 ==> (forall (y:nat{y <= length text - length pattern}). belongs text pattern y = false)))
  = bmh_gives_minus_one_belongs_false text pattern 0 0