Definition LP_teq_subst_shift := 
fun (i : nat) (u t : Term) => teq_subst_shift i 0 u t (le_0_n i)
     : forall (i : nat) (u t : Term), sub (S i) (Shift u) (Shift t) = Shift (sub i u t).
