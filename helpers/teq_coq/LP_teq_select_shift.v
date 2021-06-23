Definition LP_teq_select_shift := 
fun (i id : nat) (V : Term) =>
eq_ind_r (fun t : Term => t = Shift (dbselect i id V (var id) (var (dbprev id))))
  (eq_ind (Shift (dbselect i id V (var id) (var (dbprev id))))
     (fun t : Term => t = Shift (dbselect i id V (var id) (var (dbprev id)))) eq_refl
     (dbselect i id (Shift V) (Shift (var id)) (Shift (var (dbprev id))))
     (teq_shift_dbselect0 i id V (var id) (var (dbprev id))))
  (teq_dbselect_Sn i id (Shift V) (var (S id)))
     : forall (i id : nat) (V : Term),
       dbselect (S i) (S id) (Shift V) (var (S id)) (var id) =
       Shift (dbselect i id V (var id) (var (dbprev id))).
