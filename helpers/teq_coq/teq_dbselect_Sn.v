Definition teq_dbselect_Sn := 
fun (i n : nat) (eqT gtT : Term) =>
nat_ind (fun i0 : nat => dbselect i0 n eqT gtT (var n) = dbselect i0 n eqT gtT (var (S (dbprev n))))
  (nat_ind
     (fun n0 : nat => dbselect 0 n0 eqT gtT (var n0) = dbselect 0 n0 eqT gtT (var (S (dbprev n0))))
     eq_refl
     (fun (n0 : nat)
        (_ : dbselect 0 n0 eqT gtT (var n0) = dbselect 0 n0 eqT gtT (var (S (dbprev n0)))) => eq_refl)
     n)
  (fun (i0 : nat) (IHi : dbselect i0 n eqT gtT (var n) = dbselect i0 n eqT gtT (var (S (dbprev n))))
   =>
   nat_ind
     (fun n0 : nat =>
      dbselect i0 n0 eqT gtT (var n0) = dbselect i0 n0 eqT gtT (var (S (dbprev n0))) ->
      dbselect (S i0) n0 eqT gtT (var n0) = dbselect (S i0) n0 eqT gtT (var (S (dbprev n0))))
     (fun _ : dbselect i0 0 eqT gtT (var 0) = dbselect i0 0 eqT gtT (var (S (dbprev 0))) => eq_refl)
     (fun (n0 : nat)
        (_ : dbselect i0 n0 eqT gtT (var n0) = dbselect i0 n0 eqT gtT (var (S (dbprev n0))) ->
             dbselect (S i0) n0 eqT gtT (var n0) = dbselect (S i0) n0 eqT gtT (var (S (dbprev n0))))
        (_ : dbselect i0 (S n0) eqT gtT (var (S n0)) =
             dbselect i0 (S n0) eqT gtT (var (S (dbprev (S n0))))) => eq_refl) n IHi) i
     : forall (i n : nat) (eqT gtT : Term),
       dbselect i n eqT gtT (var n) = dbselect i n eqT gtT (var (S (dbprev n))).
