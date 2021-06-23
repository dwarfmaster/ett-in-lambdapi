Definition teq_subst_shift := 
fun (i j : nat) (u t : Term) =>
Term_ind
  (fun t0 : Term =>
   forall (i0 j0 : nat) (u0 : Term),
   j0 <= i0 ->
   sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t0) = shift j0 (sub i0 (Shift' j0 u0) t0))
  (fun (n i0 j0 : nat) (u0 : Term) (Hij : j0 <= i0) =>
   nat_ind
     (fun n0 : nat =>
      forall i1 j1 : nat,
      j1 <= i1 ->
      match dbshift j1 n0 with
      | 0 => var (dbshift j1 n0)
      | S j2 =>
          dbselect i1 j2 (shift j1 (Shift' j1 u0)) (var (dbshift j1 n0))
            (var (dbprev (dbshift j1 n0)))
      end = shift j1 (dbselect i1 n0 (Shift' j1 u0) (var n0) (var (dbprev n0))))
     (fun (i1 j1 : nat) (Hij0 : j1 <= i1) =>
      match
        i1 as n0
        return
          (j1 <= n0 ->
           match dbshift j1 0 with
           | 0 => var (dbshift j1 0)
           | S j2 =>
               dbselect n0 j2 (shift j1 (Shift' j1 u0)) (var (dbshift j1 0))
                 (var (dbprev (dbshift j1 0)))
           end = shift j1 (dbselect n0 0 (Shift' j1 u0) (var 0) (var 0)))
      with
      | 0 =>
          fun Hij1 : j1 <= 0 =>
          match
            j1 as n0
            return
              (n0 <= 0 ->
               match dbshift n0 0 with
               | 0 => var (dbshift n0 0)
               | S j2 =>
                   dbselect 0 j2 (shift n0 (Shift' n0 u0)) (var (dbshift n0 0))
                     (var (dbprev (dbshift n0 0)))
               end = shift n0 (dbselect 0 0 (Shift' n0 u0) (var 0) (var 0)))
          with
          | 0 => fun _ : 0 <= 0 => eq_refl
          | S j2 =>
              fun Hij2 : S j2 <= 0 =>
              let H : 0 = 0 -> var 0 = shift (S j2) (Shift (Shift' j2 u0)) :=
                match
                  Hij2 in (_ <= n0) return (n0 = 0 -> var 0 = shift (S j2) (Shift (Shift' j2 u0)))
                with
                | le_n _ =>
                    fun H : S j2 = 0 =>
                    (fun H0 : S j2 = 0 =>
                     let H1 : False :=
                       eq_ind (S j2) (fun e : nat => match e with
                                                     | 0 => False
                                                     | S _ => True
                                                     end) I 0 H0 in
                     False_ind (var 0 = shift (S j2) (Shift (Shift' j2 u0))) H1) H
                | le_S _ m H =>
                    fun H0 : S m = 0 =>
                    (fun H1 : S m = 0 =>
                     let H2 : False :=
                       eq_ind (S m) (fun e : nat => match e with
                                                    | 0 => False
                                                    | S _ => True
                                                    end) I 0 H1 in
                     False_ind (S j2 <= m -> var 0 = shift (S j2) (Shift (Shift' j2 u0))) H2) H0 H
                end in
              H eq_refl
          end Hij1
      | S i2 =>
          fun Hij1 : j1 <= S i2 =>
          match
            j1 as n0
            return
              (n0 <= S i2 ->
               match dbshift n0 0 with
               | 0 => var (dbshift n0 0)
               | S j2 =>
                   dbselect (S i2) j2 (shift n0 (Shift' n0 u0)) (var (dbshift n0 0))
                     (var (dbprev (dbshift n0 0)))
               end = shift n0 (dbselect (S i2) 0 (Shift' n0 u0) (var 0) (var 0)))
          with
          | 0 => fun _ : 0 <= S i2 => eq_refl
          | S j2 => fun _ : S j2 <= S i2 => eq_refl
          end Hij1
      end Hij0)
     (fun (n0 : nat)
        (IHn : forall i1 j1 : nat,
               j1 <= i1 ->
               match dbshift j1 n0 with
               | 0 => var (dbshift j1 n0)
               | S j2 =>
                   dbselect i1 j2 (shift j1 (Shift' j1 u0)) (var (dbshift j1 n0))
                     (var (dbprev (dbshift j1 n0)))
               end = shift j1 (dbselect i1 n0 (Shift' j1 u0) (var n0) (var (dbprev n0))))
        (i1 j1 : nat) (Hij0 : j1 <= i1) =>
      match
        i1 as n1
        return
          (j1 <= n1 ->
           match dbshift j1 (S n0) with
           | 0 => var (dbshift j1 (S n0))
           | S j2 =>
               dbselect n1 j2 (shift j1 (Shift' j1 u0)) (var (dbshift j1 (S n0)))
                 (var (dbprev (dbshift j1 (S n0))))
           end = shift j1 (dbselect n1 (S n0) (Shift' j1 u0) (var (S n0)) (var n0)))
      with
      | 0 =>
          fun Hij1 : j1 <= 0 =>
          match
            j1 as n1
            return
              (n1 <= 0 ->
               match dbshift n1 (S n0) with
               | 0 => var (dbshift n1 (S n0))
               | S j2 =>
                   dbselect 0 j2 (shift n1 (Shift' n1 u0)) (var (dbshift n1 (S n0)))
                     (var (dbprev (dbshift n1 (S n0))))
               end = shift n1 (dbselect 0 (S n0) (Shift' n1 u0) (var (S n0)) (var n0)))
          with
          | 0 => fun _ : 0 <= 0 => eq_refl
          | S j2 =>
              fun Hij2 : S j2 <= 0 =>
              let H :
                0 = 0 ->
                match dbshift j2 n0 with
                | 0 => shift (S j2) (Shift (Shift' j2 u0))
                | S _ => var (dbshift j2 n0)
                end = var match n0 with
                          | 0 => 0
                          | S m => S (dbshift j2 m)
                          end :=
                match
                  Hij2 in (_ <= n1)
                  return
                    (n1 = 0 ->
                     match dbshift j2 n0 with
                     | 0 => shift (S j2) (Shift (Shift' j2 u0))
                     | S _ => var (dbshift j2 n0)
                     end = var match n0 with
                               | 0 => 0
                               | S m => S (dbshift j2 m)
                               end)
                with
                | le_n _ =>
                    fun H : S j2 = 0 =>
                    (fun H0 : S j2 = 0 =>
                     let H1 : False :=
                       eq_ind (S j2) (fun e : nat => match e with
                                                     | 0 => False
                                                     | S _ => True
                                                     end) I 0 H0 in
                     False_ind
                       (match dbshift j2 n0 with
                        | 0 => shift (S j2) (Shift (Shift' j2 u0))
                        | S _ => var (dbshift j2 n0)
                        end = var match n0 with
                                  | 0 => 0
                                  | S m => S (dbshift j2 m)
                                  end) H1) H
                | le_S _ m H =>
                    fun H0 : S m = 0 =>
                    (fun H1 : S m = 0 =>
                     let H2 : False :=
                       eq_ind (S m) (fun e : nat => match e with
                                                    | 0 => False
                                                    | S _ => True
                                                    end) I 0 H1 in
                     False_ind
                       (S j2 <= m ->
                        match dbshift j2 n0 with
                        | 0 => shift (S j2) (Shift (Shift' j2 u0))
                        | S _ => var (dbshift j2 n0)
                        end = var match n0 with
                                  | 0 => 0
                                  | S m0 => S (dbshift j2 m0)
                                  end) H2) H0 H
                end in
              H eq_refl
          end Hij1
      | S i2 =>
          fun Hij1 : j1 <= S i2 =>
          match
            j1 as n1
            return
              (n1 <= S i2 ->
               match dbshift n1 (S n0) with
               | 0 => var (dbshift n1 (S n0))
               | S j2 =>
                   dbselect (S i2) j2 (shift n1 (Shift' n1 u0)) (var (dbshift n1 (S n0)))
                     (var (dbprev (dbshift n1 (S n0))))
               end = shift n1 (dbselect (S i2) (S n0) (Shift' n1 u0) (var (S n0)) (var n0)))
          with
          | 0 =>
              fun _ : 0 <= S i2 =>
              eq_ind_r
                (fun t0 : Term => dbselect i2 n0 (shift 0 u0) (var (S (S n0))) (var (S n0)) = t0)
                eq_refl (teq_shift_dbselect 0 i2 n0 u0 (var (S n0)) (var n0))
          | S j2 =>
              fun Hij2 : S j2 <= S i2 =>
              let djn := dbshift j2 n0 in
              let Heqdjn : djn = dbshift j2 n0 := eq_refl in
              let IH :
                j2 <= i2 ->
                match dbshift j2 n0 with
                | 0 => var (dbshift j2 n0)
                | S j3 =>
                    dbselect i2 j3 (shift j2 (Shift' j2 u0)) (var (dbshift j2 n0))
                      (var (dbprev (dbshift j2 n0)))
                end = shift j2 (dbselect i2 n0 (Shift' j2 u0) (var n0) (var (dbprev n0))) := 
                IHn i2 j2 in
              let IH0 :
                j2 <= i2 ->
                match djn with
                | 0 => var djn
                | S j3 => dbselect i2 j3 (shift j2 (Shift' j2 u0)) (var djn) (var (dbprev djn))
                end = shift j2 (dbselect i2 n0 (Shift' j2 u0) (var n0) (var (dbprev n0))) :=
                eq_ind_r
                  (fun n1 : nat =>
                   j2 <= i2 ->
                   match n1 with
                   | 0 => var n1
                   | S j3 => dbselect i2 j3 (shift j2 (Shift' j2 u0)) (var n1) (var (dbprev n1))
                   end = shift j2 (dbselect i2 n0 (Shift' j2 u0) (var n0) (var (dbprev n0)))) IH
                  Heqdjn in
              match
                djn as n1
                return
                  (n1 = dbshift j2 n0 ->
                   (j2 <= i2 ->
                    match n1 with
                    | 0 => var n1
                    | S j3 => dbselect i2 j3 (shift j2 (Shift' j2 u0)) (var n1) (var (dbprev n1))
                    end = shift j2 (dbselect i2 n0 (Shift' j2 u0) (var n0) (var (dbprev n0)))) ->
                   match n1 with
                   | 0 => var (S n1)
                   | S j3 =>
                       dbselect i2 j3 (shift (S j2) (Shift (Shift' j2 u0))) (var (S n1)) (var n1)
                   end = shift (S j2) (dbselect i2 n0 (Shift (Shift' j2 u0)) (var (S n0)) (var n0)))
              with
              | 0 =>
                  fun (_ : 0 = dbshift j2 n0)
                    (IH1 : j2 <= i2 ->
                           var 0 = shift j2 (dbselect i2 n0 (Shift' j2 u0) (var n0) (var (dbprev n0))))
                  =>
                  eq_ind_r (fun t0 : Term => var 1 = shift (S j2) t0)
                    (eq_ind (Shift (dbselect i2 n0 (Shift' j2 u0) (var n0) (var (dbprev n0))))
                       (fun t0 : Term => Shift (var 0) = shift (S j2) t0)
                       (eq_ind
                          (Shift (shift j2 (dbselect i2 n0 (Shift' j2 u0) (var n0) (var (dbprev n0)))))
                          (fun t0 : Term => Shift (var 0) = t0)
                          (let H :
                             var 0 =
                             shift j2 (dbselect i2 n0 (Shift' j2 u0) (var n0) (var (dbprev n0))) :=
                             IH1 (le_S_n j2 i2 Hij2) in
                           (fun
                              H0 : var 0 =
                                   shift j2 (dbselect i2 n0 (Shift' j2 u0) (var n0) (var (dbprev n0)))
                            =>
                            eq_trans (f_equal (fun f : Term -> Term => f (var 0)) eq_refl)
                              (f_equal Shift H0)) H)
                          (shift (S j2)
                             (Shift (dbselect i2 n0 (Shift' j2 u0) (var n0) (var (dbprev n0)))))
                          (teq_shift_shift0 j2
                             (dbselect i2 n0 (Shift' j2 u0) (var n0) (var (dbprev n0)))))
                       (dbselect i2 n0 (Shift (Shift' j2 u0)) (Shift (var n0))
                          (Shift (var (dbprev n0))))
                       (teq_shift_dbselect0 i2 n0 (Shift' j2 u0) (var n0) (var (dbprev n0))))
                    (teq_dbselect_Sn i2 n0 (Shift (Shift' j2 u0)) (var (S n0)))
              | S djn0 =>
                  fun (_ : S djn0 = dbshift j2 n0)
                    (IH1 : j2 <= i2 ->
                           dbselect i2 djn0 (shift j2 (Shift' j2 u0)) (var (S djn0))
                             (var (dbprev (S djn0))) =
                           shift j2 (dbselect i2 n0 (Shift' j2 u0) (var n0) (var (dbprev n0)))) =>
                  eq_ind_r
                    (fun t0 : Term =>
                     dbselect i2 djn0 (shift (S j2) (Shift (Shift' j2 u0))) 
                       (var (S (S djn0))) (var (S djn0)) = shift (S j2) t0)
                    (eq_ind (Shift (shift j2 (Shift' j2 u0)))
                       (fun t0 : Term =>
                        dbselect i2 djn0 t0 (Shift (Shift (var djn0))) (Shift (var djn0)) =
                        shift (S j2)
                          (dbselect i2 n0 (Shift (Shift' j2 u0)) (Shift (var n0))
                             (Shift (var (dbprev n0)))))
                       (eq_ind
                          (Shift
                             (dbselect i2 djn0 (shift j2 (Shift' j2 u0)) (Shift (var djn0)) (var djn0)))
                          (fun t0 : Term =>
                           t0 =
                           shift (S j2)
                             (dbselect i2 n0 (Shift (Shift' j2 u0)) (Shift (var n0))
                                (Shift (var (dbprev n0)))))
                          (eq_ind_r
                             (fun t0 : Term =>
                              Shift t0 =
                              shift (S j2)
                                (dbselect i2 n0 (Shift (Shift' j2 u0)) (Shift (var n0))
                                   (Shift (var (dbprev n0)))))
                             (eq_ind
                                (Shift (dbselect i2 n0 (Shift' j2 u0) (var n0) (var (dbprev n0))))
                                (fun t0 : Term =>
                                 Shift
                                   (dbselect i2 djn0 (shift j2 (Shift' j2 u0)) 
                                      (Shift (var djn0)) (Shift (var (dbprev djn0)))) =
                                 shift (S j2) t0)
                                (eq_ind
                                   (Shift
                                      (shift j2
                                         (dbselect i2 n0 (Shift' j2 u0) (var n0) (var (dbprev n0)))))
                                   (fun t0 : Term =>
                                    Shift
                                      (dbselect i2 djn0 (shift j2 (Shift' j2 u0)) 
                                         (Shift (var djn0)) (Shift (var (dbprev djn0)))) = t0)
                                   (let H :
                                      dbselect i2 djn0 (shift j2 (Shift' j2 u0)) 
                                        (Shift (var djn0)) (Shift (var (dbprev djn0))) =
                                      shift j2
                                        (dbselect i2 n0 (Shift' j2 u0) (var n0) (var (dbprev n0))) :=
                                      eq_ind
                                        (dbselect i2 djn0 (shift j2 (Shift' j2 u0)) 
                                           (var (S djn0)) (var djn0))
                                        (fun t0 : Term =>
                                         t0 =
                                         shift j2 (dbselect i2 n0 (Shift' j2 u0) (var n0) (var ...)))
                                        (IH1 (le_S_n j2 i2 Hij2))
                                        (dbselect i2 djn0 (shift j2 (Shift' j2 u0)) 
                                           (var (S djn0)) (var (S (dbprev djn0))))
                                        (teq_dbselect_Sn i2 djn0 (shift j2 (Shift' j2 u0))
                                           (var (S djn0))) in
                                    (fun
                                       H0 : dbselect i2 djn0 (shift j2 (...)) 
                                              (Shift (...)) (Shift (...)) =
                                            shift j2 (dbselect i2 n0 (...) (...) (...)) =>
                                     eq_trans (f_equal (fun f : ... => f (...)) eq_refl)
                                       (f_equal Shift H0)) H)
                                   (shift (S j2)
                                      (Shift
                                         (dbselect i2 n0 (Shift' j2 u0) (var n0) (var (dbprev n0)))))
                                   (teq_shift_shift0 j2
                                      (dbselect i2 n0 (Shift' j2 u0) (var n0) (var (dbprev n0)))))
                                (dbselect i2 n0 (Shift (Shift' j2 u0)) (Shift (var n0))
                                   (Shift (var (dbprev n0))))
                                (teq_shift_dbselect0 i2 n0 (Shift' j2 u0) (var n0) (var (dbprev n0))))
                             (teq_dbselect_Sn i2 djn0 (shift j2 (Shift' j2 u0)) (Shift (var djn0))))
                          (dbselect i2 djn0 (Shift (shift j2 (Shift' j2 u0)))
                             (Shift (Shift (var djn0))) (Shift (var djn0)))
                          (teq_shift_dbselect0 i2 djn0 (shift j2 (Shift' j2 u0)) 
                             (Shift (var djn0)) (var djn0))) (shift (S j2) (Shift (Shift' j2 u0)))
                       (teq_shift_shift0 j2 (Shift' j2 u0)))
                    (teq_dbselect_Sn i2 n0 (Shift (Shift' j2 u0)) (var (S n0)))
              end Heqdjn IH0
          end Hij1
      end Hij0) n i0 j0 Hij)
  (fun (t1 : Term)
     (IHt1 : forall (i0 j0 : nat) (u0 : Term),
             j0 <= i0 ->
             sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t1) = shift j0 (sub i0 (Shift' j0 u0) t1))
     (t2 : Term)
     (IHt2 : forall (i0 j0 : nat) (u0 : Term),
             j0 <= i0 ->
             sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t2) = shift j0 (sub i0 (Shift' j0 u0) t2))
     (t3 : Term)
     (IHt3 : forall (i0 j0 : nat) (u0 : Term),
             j0 <= i0 ->
             sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t3) = shift j0 (sub i0 (Shift' j0 u0) t3))
     (i0 j0 : nat) (u0 : Term) (Hij : j0 <= i0) =>
   eq_ind_r
     (fun t0 : Term =>
      tabs (sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t1)) (sub (S (S i0)) t0 (shift (S j0) t2))
        (sub (S (S i0)) t0 (shift (S j0) t3)) =
      tabs (shift j0 (sub i0 (Shift' j0 u0) t1)) (shift (S j0) (sub (S i0) (Shift (Shift' j0 u0)) t2))
        (shift (S j0) (sub (S i0) (Shift (Shift' j0 u0)) t3)))
     (eq_ind_r
        (fun t0 : Term =>
         tabs (sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t1))
           (sub (S (S i0)) (shift (S j0) (Shift' (S j0) u0)) (shift (S j0) t2)) t0 =
         tabs (shift j0 (sub i0 (Shift' j0 u0) t1)) (shift (S j0) (sub (S i0) (Shift' (S j0) u0) t2))
           (shift (S j0) (sub (S i0) (Shift' (S j0) u0) t3)))
        (eq_ind_r
           (fun t0 : Term =>
            tabs (sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t1)) t0
              (shift (S j0) (sub (S i0) (Shift' (S j0) u0) t3)) =
            tabs (shift j0 (sub i0 (Shift' j0 u0) t1))
              (shift (S j0) (sub (S i0) (Shift' (S j0) u0) t2))
              (shift (S j0) (sub (S i0) (Shift' (S j0) u0) t3)))
           (eq_ind_r
              (fun t0 : Term =>
               tabs t0 (shift (S j0) (sub (S i0) (Shift' (S j0) u0) t2))
                 (shift (S j0) (sub (S i0) (Shift' (S j0) u0) t3)) =
               tabs (shift j0 (sub i0 (Shift' j0 u0) t1))
                 (shift (S j0) (sub (S i0) (Shift' (S j0) u0) t2))
                 (shift (S j0) (sub (S i0) (Shift' (S j0) u0) t3))) eq_refl 
              (IHt1 i0 j0 u0 Hij)) (IHt2 (S i0) (S j0) u0 (le_n_S j0 i0 Hij)))
        (IHt3 (S i0) (S j0) u0 (le_n_S j0 i0 Hij))) (teq_shift_shift0 j0 (Shift' j0 u0)))
  (fun (t1 : Term)
     (IHt1 : forall (i0 j0 : nat) (u0 : Term),
             j0 <= i0 ->
             sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t1) = shift j0 (sub i0 (Shift' j0 u0) t1))
     (t2 : Term)
     (IHt2 : forall (i0 j0 : nat) (u0 : Term),
             j0 <= i0 ->
             sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t2) = shift j0 (sub i0 (Shift' j0 u0) t2))
     (t3 : Term)
     (IHt3 : forall (i0 j0 : nat) (u0 : Term),
             j0 <= i0 ->
             sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t3) = shift j0 (sub i0 (Shift' j0 u0) t3))
     (t4 : Term)
     (IHt4 : forall (i0 j0 : nat) (u0 : Term),
             j0 <= i0 ->
             sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t4) = shift j0 (sub i0 (Shift' j0 u0) t4))
     (i0 j0 : nat) (u0 : Term) (Hij : j0 <= i0) =>
   eq_ind_r
     (fun t0 : Term =>
      tapp (sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t1)) (sub (S (S i0)) t0 (shift (S j0) t2))
        (sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t3))
        (sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t4)) =
      tapp (shift j0 (sub i0 (Shift' j0 u0) t1)) (shift (S j0) (sub (S i0) (Shift (Shift' j0 u0)) t2))
        (shift j0 (sub i0 (Shift' j0 u0) t3)) (shift j0 (sub i0 (Shift' j0 u0) t4)))
     (eq_ind_r
        (fun t0 : Term =>
         tapp (sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t1))
           (sub (S (S i0)) (shift (S j0) (Shift' (S j0) u0)) (shift (S j0) t2))
           (sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t3)) t0 =
         tapp (shift j0 (sub i0 (Shift' j0 u0) t1)) (shift (S j0) (sub (S i0) (Shift' (S j0) u0) t2))
           (shift j0 (sub i0 (Shift' j0 u0) t3)) (shift j0 (sub i0 (Shift' j0 u0) t4)))
        (eq_ind_r
           (fun t0 : Term =>
            tapp (sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t1))
              (sub (S (S i0)) (shift (S j0) (Shift' (S j0) u0)) (shift (S j0) t2)) t0
              (shift j0 (sub i0 (Shift' j0 u0) t4)) =
            tapp (shift j0 (sub i0 (Shift' j0 u0) t1))
              (shift (S j0) (sub (S i0) (Shift' (S j0) u0) t2)) (shift j0 (sub i0 (Shift' j0 u0) t3))
              (shift j0 (sub i0 (Shift' j0 u0) t4)))
           (eq_ind_r
              (fun t0 : Term =>
               tapp (sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t1)) t0
                 (shift j0 (sub i0 (Shift' j0 u0) t3)) (shift j0 (sub i0 (Shift' j0 u0) t4)) =
               tapp (shift j0 (sub i0 (Shift' j0 u0) t1))
                 (shift (S j0) (sub (S i0) (Shift' (S j0) u0) t2))
                 (shift j0 (sub i0 (Shift' j0 u0) t3)) (shift j0 (sub i0 (Shift' j0 u0) t4)))
              (eq_ind_r
                 (fun t0 : Term =>
                  tapp t0 (shift (S j0) (sub (S i0) (Shift' (S j0) u0) t2))
                    (shift j0 (sub i0 (Shift' j0 u0) t3)) (shift j0 (sub i0 (Shift' j0 u0) t4)) =
                  tapp (shift j0 (sub i0 (Shift' j0 u0) t1))
                    (shift (S j0) (sub (S i0) (Shift' (S j0) u0) t2))
                    (shift j0 (sub i0 (Shift' j0 u0) t3)) (shift j0 (sub i0 (Shift' j0 u0) t4)))
                 eq_refl (IHt1 i0 j0 u0 Hij)) (IHt2 (S i0) (S j0) u0 (le_n_S j0 i0 Hij)))
           (IHt3 i0 j0 u0 Hij)) (IHt4 i0 j0 u0 Hij)) (teq_shift_shift0 j0 (Shift' j0 u0)))
  (fun (t1 : Term)
     (IHt1 : forall (i0 j0 : nat) (u0 : Term),
             j0 <= i0 ->
             sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t1) = shift j0 (sub i0 (Shift' j0 u0) t1))
     (t2 : Term)
     (IHt2 : forall (i0 j0 : nat) (u0 : Term),
             j0 <= i0 ->
             sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t2) = shift j0 (sub i0 (Shift' j0 u0) t2))
     (i0 j0 : nat) (u0 : Term) (Hij : j0 <= i0) =>
   eq_ind_r
     (fun t0 : Term =>
      tfun (sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t1)) (sub (S (S i0)) t0 (shift (S j0) t2)) =
      tfun (shift j0 (sub i0 (Shift' j0 u0) t1)) (shift (S j0) (sub (S i0) (Shift (Shift' j0 u0)) t2)))
     (eq_ind_r
        (fun t0 : Term =>
         tfun (sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t1)) t0 =
         tfun (shift j0 (sub i0 (Shift' j0 u0) t1)) (shift (S j0) (sub (S i0) (Shift' (S j0) u0) t2)))
        (eq_ind_r
           (fun t0 : Term =>
            tfun t0 (shift (S j0) (sub (S i0) (Shift' (S j0) u0) t2)) =
            tfun (shift j0 (sub i0 (Shift' j0 u0) t1))
              (shift (S j0) (sub (S i0) (Shift' (S j0) u0) t2))) eq_refl (IHt1 i0 j0 u0 Hij))
        (IHt2 (S i0) (S j0) u0 (le_n_S j0 i0 Hij))) (teq_shift_shift0 j0 (Shift' j0 u0)))
  (fun (n i0 j0 : nat) (u0 : Term) (_ : j0 <= i0) => eq_refl)
  (fun (t1 : Term)
     (IHt1 : forall (i0 j0 : nat) (u0 : Term),
             j0 <= i0 ->
             sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t1) = shift j0 (sub i0 (Shift' j0 u0) t1))
     (t2 : Term)
     (IHt2 : forall (i0 j0 : nat) (u0 : Term),
             j0 <= i0 ->
             sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t2) = shift j0 (sub i0 (Shift' j0 u0) t2))
     (t3 : Term)
     (IHt3 : forall (i0 j0 : nat) (u0 : Term),
             j0 <= i0 ->
             sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t3) = shift j0 (sub i0 (Shift' j0 u0) t3))
     (t4 : Term)
     (IHt4 : forall (i0 j0 : nat) (u0 : Term),
             j0 <= i0 ->
             sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t4) = shift j0 (sub i0 (Shift' j0 u0) t4))
     (i0 j0 : nat) (u0 : Term) (Hij : j0 <= i0) =>
   eq_ind_r
     (fun t0 : Term =>
      tpair (sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t1)) (sub (S (S i0)) t0 (shift (S j0) t2))
        (sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t3))
        (sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t4)) =
      tpair (shift j0 (sub i0 (Shift' j0 u0) t1))
        (shift (S j0) (sub (S i0) (Shift (Shift' j0 u0)) t2)) (shift j0 (sub i0 (Shift' j0 u0) t3))
        (shift j0 (sub i0 (Shift' j0 u0) t4)))
     (eq_ind_r
        (fun t0 : Term =>
         tpair (sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t1))
           (sub (S (S i0)) (shift (S j0) (Shift' (S j0) u0)) (shift (S j0) t2))
           (sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t3)) t0 =
         tpair (shift j0 (sub i0 (Shift' j0 u0) t1)) (shift (S j0) (sub (S i0) (Shift' (S j0) u0) t2))
           (shift j0 (sub i0 (Shift' j0 u0) t3)) (shift j0 (sub i0 (Shift' j0 u0) t4)))
        (eq_ind_r
           (fun t0 : Term =>
            tpair (sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t1))
              (sub (S (S i0)) (shift (S j0) (Shift' (S j0) u0)) (shift (S j0) t2)) t0
              (shift j0 (sub i0 (Shift' j0 u0) t4)) =
            tpair (shift j0 (sub i0 (Shift' j0 u0) t1))
              (shift (S j0) (sub (S i0) (Shift' (S j0) u0) t2)) (shift j0 (sub i0 (Shift' j0 u0) t3))
              (shift j0 (sub i0 (Shift' j0 u0) t4)))
           (eq_ind_r
              (fun t0 : Term =>
               tpair (sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t1)) t0
                 (shift j0 (sub i0 (Shift' j0 u0) t3)) (shift j0 (sub i0 (Shift' j0 u0) t4)) =
               tpair (shift j0 (sub i0 (Shift' j0 u0) t1))
                 (shift (S j0) (sub (S i0) (Shift' (S j0) u0) t2))
                 (shift j0 (sub i0 (Shift' j0 u0) t3)) (shift j0 (sub i0 (Shift' j0 u0) t4)))
              (eq_ind_r
                 (fun t0 : Term =>
                  tpair t0 (shift (S j0) (sub (S i0) (Shift' (S j0) u0) t2))
                    (shift j0 (sub i0 (Shift' j0 u0) t3)) (shift j0 (sub i0 (Shift' j0 u0) t4)) =
                  tpair (shift j0 (sub i0 (Shift' j0 u0) t1))
                    (shift (S j0) (sub (S i0) (Shift' (S j0) u0) t2))
                    (shift j0 (sub i0 (Shift' j0 u0) t3)) (shift j0 (sub i0 (Shift' j0 u0) t4)))
                 eq_refl (IHt1 i0 j0 u0 Hij)) (IHt2 (S i0) (S j0) u0 (le_n_S j0 i0 Hij)))
           (IHt3 i0 j0 u0 Hij)) (IHt4 i0 j0 u0 Hij)) (teq_shift_shift0 j0 (Shift' j0 u0)))
  (fun (t1 : Term)
     (IHt1 : forall (i0 j0 : nat) (u0 : Term),
             j0 <= i0 ->
             sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t1) = shift j0 (sub i0 (Shift' j0 u0) t1))
     (t2 : Term)
     (IHt2 : forall (i0 j0 : nat) (u0 : Term),
             j0 <= i0 ->
             sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t2) = shift j0 (sub i0 (Shift' j0 u0) t2))
     (t3 : Term)
     (IHt3 : forall (i0 j0 : nat) (u0 : Term),
             j0 <= i0 ->
             sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t3) = shift j0 (sub i0 (Shift' j0 u0) t3))
     (i0 j0 : nat) (u0 : Term) (Hij : j0 <= i0) =>
   eq_ind_r
     (fun t0 : Term =>
      tp1 (sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t1)) (sub (S (S i0)) t0 (shift (S j0) t2))
        (sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t3)) =
      tp1 (shift j0 (sub i0 (Shift' j0 u0) t1)) (shift (S j0) (sub (S i0) (Shift (Shift' j0 u0)) t2))
        (shift j0 (sub i0 (Shift' j0 u0) t3)))
     (eq_ind_r
        (fun t0 : Term =>
         tp1 (sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t1))
           (sub (S (S i0)) (shift (S j0) (Shift' (S j0) u0)) (shift (S j0) t2)) t0 =
         tp1 (shift j0 (sub i0 (Shift' j0 u0) t1)) (shift (S j0) (sub (S i0) (Shift' (S j0) u0) t2))
           (shift j0 (sub i0 (Shift' j0 u0) t3)))
        (eq_ind_r
           (fun t0 : Term =>
            tp1 (sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t1)) t0
              (shift j0 (sub i0 (Shift' j0 u0) t3)) =
            tp1 (shift j0 (sub i0 (Shift' j0 u0) t1))
              (shift (S j0) (sub (S i0) (Shift' (S j0) u0) t2)) (shift j0 (sub i0 (Shift' j0 u0) t3)))
           (eq_ind_r
              (fun t0 : Term =>
               tp1 t0 (shift (S j0) (sub (S i0) (Shift' (S j0) u0) t2))
                 (shift j0 (sub i0 (Shift' j0 u0) t3)) =
               tp1 (shift j0 (sub i0 (Shift' j0 u0) t1))
                 (shift (S j0) (sub (S i0) (Shift' (S j0) u0) t2))
                 (shift j0 (sub i0 (Shift' j0 u0) t3))) eq_refl (IHt1 i0 j0 u0 Hij))
           (IHt2 (S i0) (S j0) u0 (le_n_S j0 i0 Hij))) (IHt3 i0 j0 u0 Hij))
     (teq_shift_shift0 j0 (Shift' j0 u0)))
  (fun (t1 : Term)
     (IHt1 : forall (i0 j0 : nat) (u0 : Term),
             j0 <= i0 ->
             sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t1) = shift j0 (sub i0 (Shift' j0 u0) t1))
     (t2 : Term)
     (IHt2 : forall (i0 j0 : nat) (u0 : Term),
             j0 <= i0 ->
             sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t2) = shift j0 (sub i0 (Shift' j0 u0) t2))
     (t3 : Term)
     (IHt3 : forall (i0 j0 : nat) (u0 : Term),
             j0 <= i0 ->
             sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t3) = shift j0 (sub i0 (Shift' j0 u0) t3))
     (i0 j0 : nat) (u0 : Term) (Hij : j0 <= i0) =>
   eq_ind_r
     (fun t0 : Term =>
      tp2 (sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t1)) (sub (S (S i0)) t0 (shift (S j0) t2))
        (sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t3)) =
      tp2 (shift j0 (sub i0 (Shift' j0 u0) t1)) (shift (S j0) (sub (S i0) (Shift (Shift' j0 u0)) t2))
        (shift j0 (sub i0 (Shift' j0 u0) t3)))
     (eq_ind_r
        (fun t0 : Term =>
         tp2 (sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t1))
           (sub (S (S i0)) (shift (S j0) (Shift' (S j0) u0)) (shift (S j0) t2)) t0 =
         tp2 (shift j0 (sub i0 (Shift' j0 u0) t1)) (shift (S j0) (sub (S i0) (Shift' (S j0) u0) t2))
           (shift j0 (sub i0 (Shift' j0 u0) t3)))
        (eq_ind_r
           (fun t0 : Term =>
            tp2 (sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t1)) t0
              (shift j0 (sub i0 (Shift' j0 u0) t3)) =
            tp2 (shift j0 (sub i0 (Shift' j0 u0) t1))
              (shift (S j0) (sub (S i0) (Shift' (S j0) u0) t2)) (shift j0 (sub i0 (Shift' j0 u0) t3)))
           (eq_ind_r
              (fun t0 : Term =>
               tp2 t0 (shift (S j0) (sub (S i0) (Shift' (S j0) u0) t2))
                 (shift j0 (sub i0 (Shift' j0 u0) t3)) =
               tp2 (shift j0 (sub i0 (Shift' j0 u0) t1))
                 (shift (S j0) (sub (S i0) (Shift' (S j0) u0) t2))
                 (shift j0 (sub i0 (Shift' j0 u0) t3))) eq_refl (IHt1 i0 j0 u0 Hij))
           (IHt2 (S i0) (S j0) u0 (le_n_S j0 i0 Hij))) (IHt3 i0 j0 u0 Hij))
     (teq_shift_shift0 j0 (Shift' j0 u0)))
  (fun (t1 : Term)
     (IHt1 : forall (i0 j0 : nat) (u0 : Term),
             j0 <= i0 ->
             sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t1) = shift j0 (sub i0 (Shift' j0 u0) t1))
     (t2 : Term)
     (IHt2 : forall (i0 j0 : nat) (u0 : Term),
             j0 <= i0 ->
             sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t2) = shift j0 (sub i0 (Shift' j0 u0) t2))
     (i0 j0 : nat) (u0 : Term) (Hij : j0 <= i0) =>
   eq_ind_r
     (fun t0 : Term =>
      tsum (sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t1)) (sub (S (S i0)) t0 (shift (S j0) t2)) =
      tsum (shift j0 (sub i0 (Shift' j0 u0) t1)) (shift (S j0) (sub (S i0) (Shift (Shift' j0 u0)) t2)))
     (eq_ind_r
        (fun t0 : Term =>
         tsum (sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t1)) t0 =
         tsum (shift j0 (sub i0 (Shift' j0 u0) t1)) (shift (S j0) (sub (S i0) (Shift' (S j0) u0) t2)))
        (eq_ind_r
           (fun t0 : Term =>
            tsum t0 (shift (S j0) (sub (S i0) (Shift' (S j0) u0) t2)) =
            tsum (shift j0 (sub i0 (Shift' j0 u0) t1))
              (shift (S j0) (sub (S i0) (Shift' (S j0) u0) t2))) eq_refl (IHt1 i0 j0 u0 Hij))
        (IHt2 (S i0) (S j0) u0 (le_n_S j0 i0 Hij))) (teq_shift_shift0 j0 (Shift' j0 u0)))
  (fun (t1 : Term)
     (IHt1 : forall (i0 j0 : nat) (u0 : Term),
             j0 <= i0 ->
             sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t1) = shift j0 (sub i0 (Shift' j0 u0) t1))
     (t2 : Term)
     (IHt2 : forall (i0 j0 : nat) (u0 : Term),
             j0 <= i0 ->
             sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t2) = shift j0 (sub i0 (Shift' j0 u0) t2))
     (i0 j0 : nat) (u0 : Term) (Hij : j0 <= i0) =>
   eq_ind_r
     (fun t0 : Term =>
      trefl (sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t1)) t0 =
      trefl (shift j0 (sub i0 (Shift' j0 u0) t1)) (shift j0 (sub i0 (Shift' j0 u0) t2)))
     (eq_ind_r
        (fun t0 : Term =>
         trefl t0 (shift j0 (sub i0 (Shift' j0 u0) t2)) =
         trefl (shift j0 (sub i0 (Shift' j0 u0) t1)) (shift j0 (sub i0 (Shift' j0 u0) t2))) eq_refl
        (IHt1 i0 j0 u0 Hij)) (IHt2 i0 j0 u0 Hij))
  (fun (t1 : Term)
     (IHt1 : forall (i0 j0 : nat) (u0 : Term),
             j0 <= i0 ->
             sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t1) = shift j0 (sub i0 (Shift' j0 u0) t1))
     (t2 : Term)
     (IHt2 : forall (i0 j0 : nat) (u0 : Term),
             j0 <= i0 ->
             sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t2) = shift j0 (sub i0 (Shift' j0 u0) t2))
     (t3 : Term)
     (IHt3 : forall (i0 j0 : nat) (u0 : Term),
             j0 <= i0 ->
             sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t3) = shift j0 (sub i0 (Shift' j0 u0) t3))
     (i0 j0 : nat) (u0 : Term) (Hij : j0 <= i0) =>
   eq_ind_r
     (fun t0 : Term =>
      teq (sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t1))
        (sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t2)) t0 =
      teq (shift j0 (sub i0 (Shift' j0 u0) t1)) (shift j0 (sub i0 (Shift' j0 u0) t2))
        (shift j0 (sub i0 (Shift' j0 u0) t3)))
     (eq_ind_r
        (fun t0 : Term =>
         teq (sub (S i0) (shift j0 (Shift' j0 u0)) (shift j0 t1)) t0
           (shift j0 (sub i0 (Shift' j0 u0) t3)) =
         teq (shift j0 (sub i0 (Shift' j0 u0) t1)) (shift j0 (sub i0 (Shift' j0 u0) t2))
           (shift j0 (sub i0 (Shift' j0 u0) t3)))
        (eq_ind_r
           (fun t0 : Term =>
            teq t0 (shift j0 (sub i0 (Shift' j0 u0) t2)) (shift j0 (sub i0 (Shift' j0 u0) t3)) =
            teq (shift j0 (sub i0 (Shift' j0 u0) t1)) (shift j0 (sub i0 (Shift' j0 u0) t2))
              (shift j0 (sub i0 (Shift' j0 u0) t3))) eq_refl (IHt1 i0 j0 u0 Hij)) 
        (IHt2 i0 j0 u0 Hij)) (IHt3 i0 j0 u0 Hij)) t i j u
     : forall (i j : nat) (u t : Term),
       j <= i -> sub (S i) (shift j (Shift' j u)) (shift j t) = shift j (sub i (Shift' j u) t).
