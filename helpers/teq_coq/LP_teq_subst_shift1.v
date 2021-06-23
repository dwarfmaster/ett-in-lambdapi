Definition LP_teq_subst_shift1 := 
fun (i : nat) (u t : Term) =>
eq_ind_r (fun t0 : Term => sub (S (S i)) t0 (Shift1 t) = Shift1 (sub (S i) (shift 0 u) t))
  (teq_subst_shift (S i) 1 u t (le_n_S 0 i (le_0_n i))) (teq_shift_shift0 0 u)
     : forall (i : nat) (u t : Term),
       sub (S (S i)) (Shift (Shift u)) (Shift1 t) = Shift1 (sub (S i) (Shift u) t).
