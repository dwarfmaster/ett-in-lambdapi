Definition teq_subst_subst := 
fun (i j : nat) (u t1 t2 : Term) =>
Term_ind
  (fun t3 : Term =>
   forall (i0 j0 : nat) (u0 t4 : Term),
   j0 <= i0 ->
   sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t4) t3) =
   sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t4)) (sub (S i0) (Shift' (S i0) u0) t3))
  (fun n : nat =>
   nat_ind
     (fun n0 : nat =>
      forall (i0 j0 : nat) (u0 t3 : Term),
      j0 <= i0 ->
      sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) (var n0)) =
      sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) (var n0)))
     (fun (i0 j0 : nat) (u0 t3 : Term) (Hij : j0 <= i0) =>
      match
        i0 as n0
        return
          (j0 <= n0 ->
           sub n0 (Shift' n0 u0) (sub j0 (Shift' j0 t3) (var 0)) =
           sub j0 (sub n0 (Shift' n0 u0) (Shift' j0 t3)) (sub (S n0) (Shift' (S n0) u0) (var 0)))
      with
      | 0 =>
          fun Hij0 : j0 <= 0 =>
          match
            j0 as n0
            return
              (n0 <= 0 ->
               sub 0 (Shift' 0 u0) (sub n0 (Shift' n0 t3) (var 0)) =
               sub n0 (sub 0 (Shift' 0 u0) (Shift' n0 t3)) (sub 1 (Shift' 1 u0) (var 0)))
          with
          | 0 => fun _ : 0 <= 0 => eq_refl
          | S j1 =>
              fun Hij1 : S j1 <= 0 =>
              let H : 0 = 0 -> u0 = var 0 :=
                match Hij1 in (_ <= n0) return (n0 = 0 -> u0 = var 0) with
                | le_n _ =>
                    fun H : S j1 = 0 =>
                    (fun H0 : S j1 = 0 =>
                     let H1 : False :=
                       eq_ind (S j1) (fun e : nat => match e with
                                                     | 0 => False
                                                     | S _ => True
                                                     end) I 0 H0 in
                     False_ind (u0 = var 0) H1) H
                | le_S _ m H =>
                    fun H0 : S m = 0 =>
                    (fun H1 : S m = 0 =>
                     let H2 : False :=
                       eq_ind (S m) (fun e : nat => match e with
                                                    | 0 => False
                                                    | S _ => True
                                                    end) I 0 H1 in
                     False_ind (S j1 <= m -> u0 = var 0) H2) H0 H
                end in
              H eq_refl
          end Hij0
      | S i1 =>
          fun Hij0 : j0 <= S i1 =>
          match
            j0 as n0
            return
              (n0 <= S i1 ->
               sub (S i1) (Shift' (S i1) u0) (sub n0 (Shift' n0 t3) (var 0)) =
               sub n0 (sub (S i1) (Shift' (S i1) u0) (Shift' n0 t3))
                 (sub (S (S i1)) (Shift' (S (S i1)) u0) (var 0)))
          with
          | 0 => fun _ : 0 <= S i1 => eq_refl
          | S j1 => fun _ : S j1 <= S i1 => eq_refl
          end Hij0
      end Hij)
     (fun (n0 : nat)
        (IHn : forall (i0 j0 : nat) (u0 t3 : Term),
               j0 <= i0 ->
               sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) (var n0)) =
               sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) (var n0)))
        (i0 j0 : nat) (u0 t3 : Term) (Hij : j0 <= i0) =>
      match
        i0 as n1
        return
          (j0 <= n1 ->
           sub n1 (Shift' n1 u0) (sub j0 (Shift' j0 t3) (var (S n0))) =
           sub j0 (sub n1 (Shift' n1 u0) (Shift' j0 t3)) (sub (S n1) (Shift' (S n1) u0) (var (S n0))))
      with
      | 0 =>
          fun Hij0 : j0 <= 0 =>
          match
            j0 as n1
            return
              (n1 <= 0 ->
               sub 0 (Shift' 0 u0) (sub n1 (Shift' n1 t3) (var (S n0))) =
               sub n1 (sub 0 (Shift' 0 u0) (Shift' n1 t3)) (sub 1 (Shift' 1 u0) (var (S n0))))
          with
          | 0 =>
              fun _ : 0 <= 0 =>
              match
                n0 as n1
                return
                  ((forall (i1 j1 : nat) (u1 t4 : Term),
                    j1 <= i1 ->
                    sub i1 (Shift' i1 u1) (sub j1 (Shift' j1 t4) (var n1)) =
                    sub j1 (sub i1 (Shift' i1 u1) (Shift' j1 t4))
                      (sub (S i1) (Shift' (S i1) u1) (var n1))) ->
                   match n1 with
                   | 0 => u0
                   | S _ => var (dbprev n1)
                   end = sub 0 (sub 0 u0 t3) match n1 with
                                             | 0 => Shift u0
                                             | S _ => var n1
                                             end)
              with
              | 0 =>
                  fun
                    _ : forall (i1 j1 : nat) (u1 t4 : Term),
                        j1 <= i1 ->
                        sub i1 (Shift' i1 u1) (sub j1 (Shift' j1 t4) (var 0)) =
                        sub j1 (sub i1 (Shift' i1 u1) (Shift' j1 t4))
                          (sub (S i1) (Shift' (S i1) u1) (var 0)) =>
                  eq_sym (teq_shift_cancel_subst 0 (Shift' 0 (sub 0 u0 t3)) u0)
              | S n1 =>
                  fun
                    _ : forall (i1 j1 : nat) (u1 t4 : Term),
                        j1 <= i1 ->
                        sub i1 (Shift' i1 u1) (sub j1 (Shift' j1 t4) (var (S n1))) =
                        sub j1 (sub i1 (Shift' i1 u1) (Shift' j1 t4))
                          (sub (S i1) (Shift' (S i1) u1) (var (S n1))) => eq_refl
              end IHn
          | S j1 =>
              fun Hij1 : S j1 <= 0 =>
              let H :
                0 = 0 ->
                sub 0 u0 (dbselect j1 n0 (Shift (Shift' j1 t3)) (var (S n0)) (var n0)) =
                sub (S j1) (sub 0 u0 (Shift (Shift' j1 t3)))
                  match n0 with
                  | 0 => Shift u0
                  | S _ => var n0
                  end :=
                match
                  Hij1 in (_ <= n1)
                  return
                    (n1 = 0 ->
                     sub 0 u0 (dbselect j1 n0 (Shift (Shift' j1 t3)) (var (S n0)) (var n0)) =
                     sub (S j1) (sub 0 u0 (Shift (Shift' j1 t3)))
                       match n0 with
                       | 0 => Shift u0
                       | S _ => var n0
                       end)
                with
                | le_n _ =>
                    fun H : S j1 = 0 =>
                    (fun H0 : S j1 = 0 =>
                     let H1 : False :=
                       eq_ind (S j1) (fun e : nat => match e with
                                                     | 0 => False
                                                     | S _ => True
                                                     end) I 0 H0 in
                     False_ind
                       (sub 0 u0 (dbselect j1 n0 (Shift (Shift' j1 t3)) (var (S n0)) (var n0)) =
                        sub (S j1) (sub 0 u0 (Shift (Shift' j1 t3)))
                          match n0 with
                          | 0 => Shift u0
                          | S _ => var n0
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
                       (S j1 <= m ->
                        sub 0 u0 (dbselect j1 n0 (Shift (Shift' j1 t3)) (var (S n0)) (var n0)) =
                        sub (S j1) (sub 0 u0 (Shift (Shift' j1 t3)))
                          match n0 with
                          | 0 => Shift u0
                          | S _ => var n0
                          end) H2) H0 H
                end in
              H eq_refl
          end Hij0
      | S i1 =>
          fun Hij0 : j0 <= S i1 =>
          match
            j0 as n1
            return
              (n1 <= S i1 ->
               sub (S i1) (Shift' (S i1) u0) (sub n1 (Shift' n1 t3) (var (S n0))) =
               sub n1 (sub (S i1) (Shift' (S i1) u0) (Shift' n1 t3))
                 (sub (S (S i1)) (Shift' (S (S i1)) u0) (var (S n0))))
          with
          | 0 =>
              fun _ : 0 <= S i1 =>
              match
                n0 as n1
                return
                  ((forall (i2 j1 : nat) (u1 t4 : Term),
                    j1 <= i2 ->
                    sub i2 (Shift' i2 u1) (sub j1 (Shift' j1 t4) (var n1)) =
                    sub j1 (sub i2 (Shift' i2 u1) (Shift' j1 t4))
                      (sub (S i2) (Shift' (S i2) u1) (var n1))) ->
                   match n1 with
                   | 0 => var n1
                   | S j1 => dbselect i1 j1 (Shift (Shift' i1 u0)) (var n1) (var (dbprev n1))
                   end =
                   sub 0 (sub (S i1) (Shift (Shift' i1 u0)) t3)
                     match n1 with
                     | 0 => var (S n1)
                     | S j1 => dbselect i1 j1 (Shift (Shift (Shift' i1 u0))) (var (S n1)) (var n1)
                     end)
              with
              | 0 =>
                  fun
                    _ : forall (i2 j1 : nat) (u1 t4 : Term),
                        j1 <= i2 ->
                        sub i2 (Shift' i2 u1) (sub j1 (Shift' j1 t4) (var 0)) =
                        sub j1 (sub i2 (Shift' i2 u1) (Shift' j1 t4))
                          (sub (S i2) (Shift' (S i2) u1) (var 0)) => eq_refl
              | S n1 =>
                  fun
                    _ : forall (i2 j1 : nat) (u1 t4 : Term),
                        j1 <= i2 ->
                        sub i2 (Shift' i2 u1) (sub j1 (Shift' j1 t4) (var (S n1))) =
                        sub j1 (sub i2 (Shift' i2 u1) (Shift' j1 t4))
                          (sub (S i2) (Shift' (S i2) u1) (var (S n1))) =>
                  eq_ind_r
                    (fun t : Term =>
                     t =
                     sub 0 (sub (S i1) (Shift (Shift' i1 u0)) t3)
                       (dbselect i1 n1 (Shift (Shift (Shift' i1 u0))) (var (S (S n1))) (var (S n1))))
                    (eq_ind (Shift (dbselect i1 n1 (Shift' i1 u0) (var n1) (var (dbprev n1))))
                       (fun t : Term =>
                        t =
                        sub 0 (sub (S i1) (Shift (Shift' i1 u0)) t3)
                          (dbselect i1 n1 (Shift (Shift (Shift' i1 u0))) (Shift (Shift (var n1)))
                             (Shift (var n1))))
                       (eq_ind
                          (Shift (dbselect i1 n1 (Shift (Shift' i1 u0)) (Shift (var n1)) (var n1)))
                          (fun t : Term =>
                           Shift (dbselect i1 n1 (Shift' i1 u0) (var n1) (var (dbprev n1))) =
                           sub 0 (sub (S i1) (Shift (Shift' i1 u0)) t3) t)
                          (eq_ind_r
                             (fun t : Term =>
                              Shift (dbselect i1 n1 (Shift' i1 u0) (var n1) (var (dbprev n1))) =
                              sub 0 (sub (S i1) (Shift (Shift' i1 u0)) t3) (Shift t))
                             (eq_ind
                                (Shift (dbselect i1 n1 (Shift' i1 u0) (var n1) (var (dbprev n1))))
                                (fun t : Term =>
                                 Shift (dbselect i1 n1 (Shift' i1 u0) (var n1) (var (dbprev n1))) =
                                 sub 0 (sub (S i1) (Shift (Shift' i1 u0)) t3) (Shift t))
                                (eq_ind_r
                                   (fun t : Term =>
                                    shift 0 (dbselect i1 n1 (Shift' i1 u0) (var n1) (var (dbprev n1))) =
                                    t) eq_refl
                                   (teq_shift_cancel_subst 0
                                      (Shift' 0 (sub (S i1) (shift 0 (Shift' i1 u0)) t3))
                                      (shift 0
                                         (dbselect i1 n1 (Shift' i1 u0) (var n1) (var (dbprev n1))))))
                                (dbselect i1 n1 (Shift (Shift' i1 u0)) (Shift (var n1))
                                   (Shift (var (dbprev n1))))
                                (teq_shift_dbselect0 i1 n1 (Shift' i1 u0) (var n1) (var (dbprev n1))))
                             (teq_dbselect_Sn i1 n1 (Shift (Shift' i1 u0)) (Shift (var n1))))
                          (dbselect i1 n1 (Shift (Shift (Shift' i1 u0))) (Shift (Shift (var n1)))
                             (Shift (var n1)))
                          (teq_shift_dbselect0 i1 n1 (Shift (Shift' i1 u0)) (Shift (var n1)) (var n1)))
                       (dbselect i1 n1 (Shift (Shift' i1 u0)) (Shift (var n1))
                          (Shift (var (dbprev n1))))
                       (teq_shift_dbselect0 i1 n1 (Shift' i1 u0) (var n1) (var (dbprev n1))))
                    (teq_dbselect_Sn i1 n1 (Shift (Shift' i1 u0)) (var (S n1)))
              end IHn
          | S j1 =>
              fun Hij1 : S j1 <= S i1 =>
              match
                n0 as n1
                return
                  ((forall (i2 j2 : nat) (u1 t4 : Term),
                    j2 <= i2 ->
                    sub i2 (Shift' i2 u1) (sub j2 (Shift' j2 t4) (var n1)) =
                    sub j2 (sub i2 (Shift' i2 u1) (Shift' j2 t4))
                      (sub (S i2) (Shift' (S i2) u1) (var n1))) ->
                   sub (S i1) (Shift (Shift' i1 u0))
                     (dbselect j1 n1 (Shift (Shift' j1 t3)) (var (S n1)) (var n1)) =
                   sub (S j1) (sub (S i1) (Shift (Shift' i1 u0)) (Shift (Shift' j1 t3)))
                     match n1 with
                     | 0 => var (S n1)
                     | S j2 => dbselect i1 j2 (Shift (Shift (Shift' i1 u0))) (var (S n1)) (var n1)
                     end)
              with
              | 0 =>
                  fun
                    IHn0 : forall (i2 j2 : nat) (u1 t4 : Term),
                           j2 <= i2 ->
                           sub i2 (Shift' i2 u1) (sub j2 (Shift' j2 t4) (var 0)) =
                           sub j2 (sub i2 (Shift' i2 u1) (Shift' j2 t4))
                             (sub (S i2) (Shift' (S i2) u1) (var 0)) =>
                  eq_ind_r
                    (fun t : Term =>
                     sub (S i1) (Shift (Shift' i1 u0)) t =
                     dbselect j1 0 (sub (S i1) (Shift (Shift' i1 u0)) (Shift (Shift' j1 t3))) 
                       (var 1) (var 0))
                    (eq_ind_r
                       (fun t : Term =>
                        sub (S i1) (Shift (Shift' i1 u0))
                          (dbselect j1 0 (Shift (Shift' j1 t3)) (var 1) (var (S (dbprev 0)))) = t)
                       (eq_ind (Shift (dbselect j1 0 (Shift' j1 t3) (var 0) (var (dbprev 0))))
                          (fun t : Term =>
                           sub (S i1) (Shift (Shift' i1 u0)) t =
                           dbselect j1 0 (sub (S i1) (Shift (Shift' i1 u0)) (Shift (Shift' j1 t3)))
                             (Shift (var 0)) (Shift (var (dbprev 0))))
                          (eq_ind_r
                             (fun t : Term =>
                              t =
                              dbselect j1 0 (sub (S i1) (Shift (Shift' i1 u0)) (Shift (Shift' j1 t3)))
                                (Shift (var 0)) (Shift (var (dbprev 0))))
                             (eq_ind_r
                                (fun t : Term =>
                                 Shift
                                   (sub i1 (Shift' i1 u0)
                                      (dbselect j1 0 (Shift' j1 t3) (var 0) (var (dbprev 0)))) =
                                 dbselect j1 0 t (Shift (var 0)) (Shift (var (dbprev 0))))
                                (eq_ind
                                   (Shift
                                      (dbselect j1 0 (sub i1 (Shift' i1 u0) (Shift' j1 t3)) 
                                         (var 0) (var (dbprev 0))))
                                   (fun t : Term =>
                                    Shift
                                      (sub i1 (Shift' i1 u0)
                                         (dbselect j1 0 (Shift' j1 t3) (var 0) (var (dbprev 0)))) = t)
                                   (let H :
                                      sub i1 (Shift' i1 u0)
                                        (dbselect j1 0 (Shift' j1 t3) (var 0) (var (dbprev 0))) =
                                      dbselect j1 0 (sub i1 (Shift' i1 u0) (Shift' j1 t3)) 
                                        (var 0) (var (dbprev 0)) :=
                                      IHn0 i1 j1 u0 t3 (le_S_n j1 i1 Hij1) in
                                    (fun
                                       H0 : sub i1 (Shift' i1 u0)
                                              (dbselect j1 0 (Shift' j1 t3) (var 0) (var (dbprev 0))) =
                                            dbselect j1 0 (sub i1 (Shift' i1 u0) (Shift' j1 t3))
                                              (var 0) (var (dbprev 0)) =>
                                     eq_trans
                                       (f_equal
                                          (fun f : Term -> Term =>
                                           f (sub i1 (Shift' i1 u0) (dbselect j1 0 (...) (...) (...))))
                                          eq_refl) (f_equal Shift H0)) H)
                                   (dbselect j1 0 (Shift (sub i1 (Shift' i1 u0) (Shift' j1 t3)))
                                      (Shift (var 0)) (Shift (var (dbprev 0))))
                                   (teq_shift_dbselect0 j1 0 (sub i1 (Shift' i1 u0) (Shift' j1 t3))
                                      (var 0) (var (dbprev 0))))
                                (LP_teq_subst_shift i1 (Shift' i1 u0) (Shift' j1 t3)))
                             (LP_teq_subst_shift i1 (Shift' i1 u0)
                                (dbselect j1 0 (Shift' j1 t3) (var 0) (var (dbprev 0)))))
                          (dbselect j1 0 (Shift (Shift' j1 t3)) (Shift (var 0))
                             (Shift (var (dbprev 0))))
                          (teq_shift_dbselect0 j1 0 (Shift' j1 t3) (var 0) (var (dbprev 0))))
                       (teq_dbselect_Sn j1 0
                          (sub (S i1) (Shift (Shift' i1 u0)) (Shift (Shift' j1 t3))) 
                          (var 1))) (teq_dbselect_Sn j1 0 (Shift (Shift' j1 t3)) (var 1))
              | S n1 =>
                  fun
                    IHn0 : forall (i2 j2 : nat) (u1 t4 : Term),
                           j2 <= i2 ->
                           sub i2 (Shift' i2 u1) (sub j2 (Shift' j2 t4) (var (S n1))) =
                           sub j2 (sub i2 (Shift' i2 u1) (Shift' j2 t4))
                             (sub (S i2) (Shift' (S i2) u1) (var (S n1))) =>
                  eq_ind_r
                    (fun t : Term =>
                     sub (S i1) (Shift (Shift' i1 u0)) t =
                     sub (S j1) (sub (S i1) (Shift (Shift' i1 u0)) (Shift (Shift' j1 t3)))
                       (dbselect i1 n1 (Shift (Shift (Shift' i1 u0))) (var (S (S n1))) (var (S n1))))
                    (eq_ind
                       (Shift
                          (dbselect j1 (S n1) (Shift' j1 t3) (Shift (var n1)) (var (dbprev (S n1)))))
                       (fun t : Term =>
                        sub (S i1) (Shift (Shift' i1 u0)) t =
                        sub (S j1) (sub (S i1) (Shift (Shift' i1 u0)) (Shift (Shift' j1 t3)))
                          (dbselect i1 n1 (Shift (Shift (Shift' i1 u0))) (Shift (Shift (var n1)))
                             (Shift (var n1))))
                       (eq_ind
                          (Shift (dbselect i1 n1 (Shift (Shift' i1 u0)) (Shift (var n1)) (var n1)))
                          (fun t : Term =>
                           sub (S i1) (Shift (Shift' i1 u0))
                             (Shift
                                (dbselect j1 (S n1) (Shift' j1 t3) (Shift (var n1))
                                   (var (dbprev (S n1))))) =
                           sub (S j1) (sub (S i1) (Shift (Shift' i1 u0)) (Shift (Shift' j1 t3))) t)
                          (eq_ind_r
                             (fun t : Term =>
                              sub (S i1) (Shift (Shift' i1 u0))
                                (Shift
                                   (dbselect j1 (S n1) (Shift' j1 t3) (Shift (var n1))
                                      (var (dbprev (S n1))))) =
                              sub (S j1) (sub (S i1) (Shift (Shift' i1 u0)) (Shift (Shift' j1 t3)))
                                (Shift t))
                             (eq_ind
                                (Shift (dbselect i1 n1 (Shift' i1 u0) (var n1) (var (dbprev n1))))
                                (fun t : Term =>
                                 sub (S i1) (Shift (Shift' i1 u0))
                                   (Shift
                                      (dbselect j1 (S n1) (Shift' j1 t3) (Shift (var n1))
                                         (var (dbprev (S n1))))) =
                                 sub (S j1) (sub (S i1) (Shift (Shift' i1 u0)) (Shift (Shift' j1 t3)))
                                   (Shift t))
                                (eq_ind_r
                                   (fun t : Term =>
                                    t =
                                    sub (S j1)
                                      (sub (S i1) (Shift (Shift' i1 u0)) (Shift (Shift' j1 t3)))
                                      (Shift
                                         (Shift
                                            (dbselect i1 n1 (Shift' i1 u0) (var n1) (var (dbprev n1))))))
                                   (eq_ind_r
                                      (fun t : Term =>
                                       Shift
                                         (sub i1 (Shift' i1 u0)
                                            (dbselect j1 (S n1) (Shift' j1 t3) 
                                               (Shift (var n1)) (var (dbprev (S n1))))) =
                                       sub (S j1) t
                                         (Shift
                                            (Shift
                                               (dbselect i1 n1 (Shift' i1 u0) 
                                                  (var n1) (var (dbprev n1))))))
                                      (eq_ind_r
                                         (fun t : Term =>
                                          Shift
                                            (sub i1 (Shift' i1 u0)
                                               (dbselect j1 (S n1) (Shift' j1 t3) 
                                                  (Shift (var n1)) (var (dbprev ...)))) = t)
                                         (let H :
                                            sub i1 (Shift' i1 u0)
                                              (dbselect j1 (S n1) (Shift' j1 t3) 
                                                 (Shift (var n1)) (var (dbprev (...)))) =
                                            sub j1 (sub i1 (Shift' i1 u0) (Shift' j1 t3))
                                              (Shift
                                                 (dbselect i1 n1 (Shift' i1 u0) (var n1) (var (...)))) :=
                                            eq_ind_r
                                              (fun t : Term =>
                                               sub i1 (Shift' i1 u0)
                                                 (dbselect j1 (S n1) (Shift' j1 t3) 
                                                    (Shift ...) (var ...)) =
                                               sub j1 (sub i1 (Shift' i1 u0) (Shift' j1 t3)) t)
                                              (eq_ind
                                                 (dbselect i1 n1 (Shift (Shift' i1 u0)) 
                                                    (var (S n1)) (var n1))
                                                 (fun t : Term =>
                                                  sub i1 (Shift' i1 u0) (dbselect j1 ... ... ... ...) =
                                                  sub j1 (sub i1 ... ...) t)
                                                 (IHn0 i1 j1 u0 t3 (le_S_n j1 i1 Hij1))
                                                 (dbselect i1 n1 (Shift (Shift' i1 u0)) 
                                                    (var (S n1)) (var (S ...)))
                                                 (teq_dbselect_Sn i1 n1 (Shift (Shift' i1 u0))
                                                    (var (S n1))))
                                              (teq_shift_dbselect0 i1 n1 (Shift' i1 u0) 
                                                 (var n1) (var (dbprev n1))) in
                                          (fun
                                             H0 : sub i1 (Shift' i1 u0)
                                                    (dbselect j1 (...) (...) (...) (...)) =
                                                  sub j1 (sub i1 (...) (...)) (Shift (...)) =>
                                           eq_trans (f_equal (fun f : ... => f (...)) eq_refl)
                                             (f_equal Shift H0)) H)
                                         (LP_teq_subst_shift j1 (sub i1 (Shift' i1 u0) (Shift' j1 t3))
                                            (Shift
                                               (dbselect i1 n1 (Shift' i1 u0) 
                                                  (var n1) (var (dbprev n1))))))
                                      (LP_teq_subst_shift i1 (Shift' i1 u0) (Shift' j1 t3)))
                                   (LP_teq_subst_shift i1 (Shift' i1 u0)
                                      (dbselect j1 (S n1) (Shift' j1 t3) (Shift (var n1))
                                         (var (dbprev (S n1))))))
                                (dbselect i1 n1 (Shift (Shift' i1 u0)) (Shift (var n1))
                                   (Shift (var (dbprev n1))))
                                (teq_shift_dbselect0 i1 n1 (Shift' i1 u0) (var n1) (var (dbprev n1))))
                             (teq_dbselect_Sn i1 n1 (Shift (Shift' i1 u0)) (Shift (var n1))))
                          (dbselect i1 n1 (Shift (Shift (Shift' i1 u0))) (Shift (Shift (var n1)))
                             (Shift (var n1)))
                          (teq_shift_dbselect0 i1 n1 (Shift (Shift' i1 u0)) (Shift (var n1)) (var n1)))
                       (dbselect j1 (S n1) (Shift (Shift' j1 t3)) (Shift (Shift (var n1)))
                          (Shift (var (dbprev (S n1)))))
                       (teq_shift_dbselect0 j1 (S n1) (Shift' j1 t3) (Shift (var n1))
                          (var (dbprev (S n1)))))
                    (teq_dbselect_Sn j1 (S n1) (Shift (Shift' j1 t3)) (var (S (S n1))))
              end IHn
          end Hij0
      end Hij) n)
  (fun (t2_1 : Term)
     (IHt2_1 : forall (i0 j0 : nat) (u0 t3 : Term),
               j0 <= i0 ->
               sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_1) =
               sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_1))
     (t2_2 : Term)
     (IHt2_2 : forall (i0 j0 : nat) (u0 t3 : Term),
               j0 <= i0 ->
               sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_2) =
               sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_2))
     (t2_3 : Term)
     (IHt2_3 : forall (i0 j0 : nat) (u0 t3 : Term),
               j0 <= i0 ->
               sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_3) =
               sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_3))
     (i0 j0 : nat) (u0 t3 : Term) (Hij : j0 <= i0) =>
   eq_ind_r
     (fun t : Term =>
      tabs (sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_1))
        (sub (S i0) (Shift' (S i0) u0) (sub (S j0) (Shift' (S j0) t3) t2_2)) t =
      tabs (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_1))
        (sub (S j0) (Shift (sub i0 (Shift' i0 u0) (Shift' j0 t3)))
           (sub (S (S i0)) (Shift' (S (S i0)) u0) t2_2))
        (sub (S j0) (Shift (sub i0 (Shift' i0 u0) (Shift' j0 t3)))
           (sub (S (S i0)) (Shift' (S (S i0)) u0) t2_3)))
     (eq_ind_r
        (fun t : Term =>
         tabs (sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_1)) t
           (sub (S j0) (sub (S i0) (Shift' (S i0) u0) (Shift' (S j0) t3))
              (sub (S (S i0)) (Shift' (S (S i0)) u0) t2_3)) =
         tabs (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_1))
           (sub (S j0) (Shift (sub i0 (Shift' i0 u0) (Shift' j0 t3)))
              (sub (S (S i0)) (Shift' (S (S i0)) u0) t2_2))
           (sub (S j0) (Shift (sub i0 (Shift' i0 u0) (Shift' j0 t3)))
              (sub (S (S i0)) (Shift' (S (S i0)) u0) t2_3)))
        (eq_ind_r
           (fun t : Term =>
            tabs t
              (sub (S j0) (sub (S i0) (Shift' (S i0) u0) (Shift' (S j0) t3))
                 (sub (S (S i0)) (Shift' (S (S i0)) u0) t2_2))
              (sub (S j0) (sub (S i0) (Shift' (S i0) u0) (Shift' (S j0) t3))
                 (sub (S (S i0)) (Shift' (S (S i0)) u0) t2_3)) =
            tabs (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_1))
              (sub (S j0) (Shift (sub i0 (Shift' i0 u0) (Shift' j0 t3)))
                 (sub (S (S i0)) (Shift' (S (S i0)) u0) t2_2))
              (sub (S j0) (Shift (sub i0 (Shift' i0 u0) (Shift' j0 t3)))
                 (sub (S (S i0)) (Shift' (S (S i0)) u0) t2_3)))
           (eq_ind (sub (S i0) (Shift (Shift' i0 u0)) (Shift (Shift' j0 t3)))
              (fun t : Term =>
               tabs
                 (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3))
                    (sub (S i0) (Shift (Shift' i0 u0)) t2_1))
                 (sub (S j0) (sub (S i0) (Shift (Shift' i0 u0)) (Shift (Shift' j0 t3)))
                    (sub (S (S i0)) (Shift (Shift (Shift' i0 u0))) t2_2))
                 (sub (S j0) (sub (S i0) (Shift (Shift' i0 u0)) (Shift (Shift' j0 t3)))
                    (sub (S (S i0)) (Shift (Shift (Shift' i0 u0))) t2_3)) =
               tabs
                 (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3))
                    (sub (S i0) (Shift (Shift' i0 u0)) t2_1))
                 (sub (S j0) t (sub (S (S i0)) (Shift (Shift (Shift' i0 u0))) t2_2))
                 (sub (S j0) t (sub (S (S i0)) (Shift (Shift (Shift' i0 u0))) t2_3))) eq_refl
              (Shift (sub i0 (Shift' i0 u0) (Shift' j0 t3)))
              (LP_teq_subst_shift i0 (Shift' i0 u0) (Shift' j0 t3))) (IHt2_1 i0 j0 u0 t3 Hij))
        (IHt2_2 (S i0) (S j0) u0 t3 (le_n_S j0 i0 Hij)))
     (IHt2_3 (S i0) (S j0) u0 t3 (le_n_S j0 i0 Hij)))
  (fun (t2_1 : Term)
     (IHt2_1 : forall (i0 j0 : nat) (u0 t3 : Term),
               j0 <= i0 ->
               sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_1) =
               sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_1))
     (t2_2 : Term)
     (IHt2_2 : forall (i0 j0 : nat) (u0 t3 : Term),
               j0 <= i0 ->
               sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_2) =
               sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_2))
     (t2_3 : Term)
     (IHt2_3 : forall (i0 j0 : nat) (u0 t3 : Term),
               j0 <= i0 ->
               sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_3) =
               sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_3))
     (t2_4 : Term)
     (IHt2_4 : forall (i0 j0 : nat) (u0 t3 : Term),
               j0 <= i0 ->
               sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_4) =
               sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_4))
     (i0 j0 : nat) (u0 t3 : Term) (Hij : j0 <= i0) =>
   eq_ind_r
     (fun t : Term =>
      tapp (sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_1))
        (sub (S i0) (Shift' (S i0) u0) (sub (S j0) (Shift' (S j0) t3) t2_2))
        (sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_3)) t =
      tapp (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_1))
        (sub (S j0) (Shift (sub i0 (Shift' i0 u0) (Shift' j0 t3)))
           (sub (S (S i0)) (Shift' (S (S i0)) u0) t2_2))
        (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_3))
        (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_4)))
     (eq_ind_r
        (fun t : Term =>
         tapp (sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_1))
           (sub (S i0) (Shift' (S i0) u0) (sub (S j0) (Shift' (S j0) t3) t2_2)) t
           (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_4)) =
         tapp (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_1))
           (sub (S j0) (Shift (sub i0 (Shift' i0 u0) (Shift' j0 t3)))
              (sub (S (S i0)) (Shift' (S (S i0)) u0) t2_2))
           (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_3))
           (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_4)))
        (eq_ind_r
           (fun t : Term =>
            tapp (sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_1)) t
              (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_3))
              (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_4)) =
            tapp (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_1))
              (sub (S j0) (Shift (sub i0 (Shift' i0 u0) (Shift' j0 t3)))
                 (sub (S (S i0)) (Shift' (S (S i0)) u0) t2_2))
              (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_3))
              (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_4)))
           (eq_ind_r
              (fun t : Term =>
               tapp t
                 (sub (S j0) (sub (S i0) (Shift' (S i0) u0) (Shift' (S j0) t3))
                    (sub (S (S i0)) (Shift' (S (S i0)) u0) t2_2))
                 (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_3))
                 (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_4)) =
               tapp
                 (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_1))
                 (sub (S j0) (Shift (sub i0 (Shift' i0 u0) (Shift' j0 t3)))
                    (sub (S (S i0)) (Shift' (S (S i0)) u0) t2_2))
                 (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_3))
                 (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_4)))
              (eq_ind (sub (S i0) (Shift (Shift' i0 u0)) (Shift (Shift' j0 t3)))
                 (fun t : Term =>
                  tapp
                    (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3))
                       (sub (S i0) (Shift (Shift' i0 u0)) t2_1))
                    (sub (S j0) (sub (S i0) (Shift (Shift' i0 u0)) (Shift (Shift' j0 t3)))
                       (sub (S (S i0)) (Shift (Shift (Shift' i0 u0))) t2_2))
                    (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3))
                       (sub (S i0) (Shift (Shift' i0 u0)) t2_3))
                    (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3))
                       (sub (S i0) (Shift (Shift' i0 u0)) t2_4)) =
                  tapp
                    (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3))
                       (sub (S i0) (Shift (Shift' i0 u0)) t2_1))
                    (sub (S j0) t (sub (S (S i0)) (Shift (Shift (Shift' i0 u0))) t2_2))
                    (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3))
                       (sub (S i0) (Shift (Shift' i0 u0)) t2_3))
                    (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3))
                       (sub (S i0) (Shift (Shift' i0 u0)) t2_4))) eq_refl
                 (Shift (sub i0 (Shift' i0 u0) (Shift' j0 t3)))
                 (LP_teq_subst_shift i0 (Shift' i0 u0) (Shift' j0 t3))) (IHt2_1 i0 j0 u0 t3 Hij))
           (IHt2_2 (S i0) (S j0) u0 t3 (le_n_S j0 i0 Hij))) (IHt2_3 i0 j0 u0 t3 Hij))
     (IHt2_4 i0 j0 u0 t3 Hij))
  (fun (t2_1 : Term)
     (IHt2_1 : forall (i0 j0 : nat) (u0 t3 : Term),
               j0 <= i0 ->
               sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_1) =
               sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_1))
     (t2_2 : Term)
     (IHt2_2 : forall (i0 j0 : nat) (u0 t3 : Term),
               j0 <= i0 ->
               sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_2) =
               sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_2))
     (i0 j0 : nat) (u0 t3 : Term) (Hij : j0 <= i0) =>
   eq_ind_r
     (fun t : Term =>
      tfun (sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_1)) t =
      tfun (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_1))
        (sub (S j0) (Shift (sub i0 (Shift' i0 u0) (Shift' j0 t3)))
           (sub (S (S i0)) (Shift' (S (S i0)) u0) t2_2)))
     (eq_ind_r
        (fun t : Term =>
         tfun t
           (sub (S j0) (sub (S i0) (Shift' (S i0) u0) (Shift' (S j0) t3))
              (sub (S (S i0)) (Shift' (S (S i0)) u0) t2_2)) =
         tfun (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_1))
           (sub (S j0) (Shift (sub i0 (Shift' i0 u0) (Shift' j0 t3)))
              (sub (S (S i0)) (Shift' (S (S i0)) u0) t2_2)))
        (eq_ind (sub (S i0) (Shift (Shift' i0 u0)) (Shift (Shift' j0 t3)))
           (fun t : Term =>
            tfun
              (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift (Shift' i0 u0)) t2_1))
              (sub (S j0) (sub (S i0) (Shift (Shift' i0 u0)) (Shift (Shift' j0 t3)))
                 (sub (S (S i0)) (Shift (Shift (Shift' i0 u0))) t2_2)) =
            tfun
              (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift (Shift' i0 u0)) t2_1))
              (sub (S j0) t (sub (S (S i0)) (Shift (Shift (Shift' i0 u0))) t2_2))) eq_refl
           (Shift (sub i0 (Shift' i0 u0) (Shift' j0 t3)))
           (LP_teq_subst_shift i0 (Shift' i0 u0) (Shift' j0 t3))) (IHt2_1 i0 j0 u0 t3 Hij))
     (IHt2_2 (S i0) (S j0) u0 t3 (le_n_S j0 i0 Hij)))
  (fun (n i0 j0 : nat) (u0 t3 : Term) (_ : j0 <= i0) => eq_refl)
  (fun (t2_1 : Term)
     (IHt2_1 : forall (i0 j0 : nat) (u0 t3 : Term),
               j0 <= i0 ->
               sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_1) =
               sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_1))
     (t2_2 : Term)
     (IHt2_2 : forall (i0 j0 : nat) (u0 t3 : Term),
               j0 <= i0 ->
               sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_2) =
               sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_2))
     (t2_3 : Term)
     (IHt2_3 : forall (i0 j0 : nat) (u0 t3 : Term),
               j0 <= i0 ->
               sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_3) =
               sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_3))
     (t2_4 : Term)
     (IHt2_4 : forall (i0 j0 : nat) (u0 t3 : Term),
               j0 <= i0 ->
               sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_4) =
               sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_4))
     (i0 j0 : nat) (u0 t3 : Term) (Hij : j0 <= i0) =>
   eq_ind_r
     (fun t : Term =>
      tpair (sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_1))
        (sub (S i0) (Shift' (S i0) u0) (sub (S j0) (Shift' (S j0) t3) t2_2))
        (sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_3)) t =
      tpair (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_1))
        (sub (S j0) (Shift (sub i0 (Shift' i0 u0) (Shift' j0 t3)))
           (sub (S (S i0)) (Shift' (S (S i0)) u0) t2_2))
        (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_3))
        (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_4)))
     (eq_ind_r
        (fun t : Term =>
         tpair (sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_1))
           (sub (S i0) (Shift' (S i0) u0) (sub (S j0) (Shift' (S j0) t3) t2_2)) t
           (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_4)) =
         tpair (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_1))
           (sub (S j0) (Shift (sub i0 (Shift' i0 u0) (Shift' j0 t3)))
              (sub (S (S i0)) (Shift' (S (S i0)) u0) t2_2))
           (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_3))
           (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_4)))
        (eq_ind_r
           (fun t : Term =>
            tpair (sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_1)) t
              (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_3))
              (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_4)) =
            tpair (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_1))
              (sub (S j0) (Shift (sub i0 (Shift' i0 u0) (Shift' j0 t3)))
                 (sub (S (S i0)) (Shift' (S (S i0)) u0) t2_2))
              (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_3))
              (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_4)))
           (eq_ind_r
              (fun t : Term =>
               tpair t
                 (sub (S j0) (sub (S i0) (Shift' (S i0) u0) (Shift' (S j0) t3))
                    (sub (S (S i0)) (Shift' (S (S i0)) u0) t2_2))
                 (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_3))
                 (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_4)) =
               tpair
                 (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_1))
                 (sub (S j0) (Shift (sub i0 (Shift' i0 u0) (Shift' j0 t3)))
                    (sub (S (S i0)) (Shift' (S (S i0)) u0) t2_2))
                 (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_3))
                 (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_4)))
              (eq_ind (sub (S i0) (Shift (Shift' i0 u0)) (Shift (Shift' j0 t3)))
                 (fun t : Term =>
                  tpair
                    (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3))
                       (sub (S i0) (Shift (Shift' i0 u0)) t2_1))
                    (sub (S j0) (sub (S i0) (Shift (Shift' i0 u0)) (Shift (Shift' j0 t3)))
                       (sub (S (S i0)) (Shift (Shift (Shift' i0 u0))) t2_2))
                    (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3))
                       (sub (S i0) (Shift (Shift' i0 u0)) t2_3))
                    (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3))
                       (sub (S i0) (Shift (Shift' i0 u0)) t2_4)) =
                  tpair
                    (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3))
                       (sub (S i0) (Shift (Shift' i0 u0)) t2_1))
                    (sub (S j0) t (sub (S (S i0)) (Shift (Shift (Shift' i0 u0))) t2_2))
                    (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3))
                       (sub (S i0) (Shift (Shift' i0 u0)) t2_3))
                    (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3))
                       (sub (S i0) (Shift (Shift' i0 u0)) t2_4))) eq_refl
                 (Shift (sub i0 (Shift' i0 u0) (Shift' j0 t3)))
                 (LP_teq_subst_shift i0 (Shift' i0 u0) (Shift' j0 t3))) (IHt2_1 i0 j0 u0 t3 Hij))
           (IHt2_2 (S i0) (S j0) u0 t3 (le_n_S j0 i0 Hij))) (IHt2_3 i0 j0 u0 t3 Hij))
     (IHt2_4 i0 j0 u0 t3 Hij))
  (fun (t2_1 : Term)
     (IHt2_1 : forall (i0 j0 : nat) (u0 t3 : Term),
               j0 <= i0 ->
               sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_1) =
               sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_1))
     (t2_2 : Term)
     (IHt2_2 : forall (i0 j0 : nat) (u0 t3 : Term),
               j0 <= i0 ->
               sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_2) =
               sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_2))
     (t2_3 : Term)
     (IHt2_3 : forall (i0 j0 : nat) (u0 t3 : Term),
               j0 <= i0 ->
               sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_3) =
               sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_3))
     (i0 j0 : nat) (u0 t3 : Term) (Hij : j0 <= i0) =>
   eq_ind_r
     (fun t : Term =>
      tp1 (sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_1))
        (sub (S i0) (Shift' (S i0) u0) (sub (S j0) (Shift' (S j0) t3) t2_2)) t =
      tp1 (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_1))
        (sub (S j0) (Shift (sub i0 (Shift' i0 u0) (Shift' j0 t3)))
           (sub (S (S i0)) (Shift' (S (S i0)) u0) t2_2))
        (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_3)))
     (eq_ind_r
        (fun t : Term =>
         tp1 (sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_1)) t
           (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_3)) =
         tp1 (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_1))
           (sub (S j0) (Shift (sub i0 (Shift' i0 u0) (Shift' j0 t3)))
              (sub (S (S i0)) (Shift' (S (S i0)) u0) t2_2))
           (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_3)))
        (eq_ind_r
           (fun t : Term =>
            tp1 t
              (sub (S j0) (sub (S i0) (Shift' (S i0) u0) (Shift' (S j0) t3))
                 (sub (S (S i0)) (Shift' (S (S i0)) u0) t2_2))
              (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_3)) =
            tp1 (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_1))
              (sub (S j0) (Shift (sub i0 (Shift' i0 u0) (Shift' j0 t3)))
                 (sub (S (S i0)) (Shift' (S (S i0)) u0) t2_2))
              (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_3)))
           (eq_ind (sub (S i0) (Shift (Shift' i0 u0)) (Shift (Shift' j0 t3)))
              (fun t : Term =>
               tp1
                 (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3))
                    (sub (S i0) (Shift (Shift' i0 u0)) t2_1))
                 (sub (S j0) (sub (S i0) (Shift (Shift' i0 u0)) (Shift (Shift' j0 t3)))
                    (sub (S (S i0)) (Shift (Shift (Shift' i0 u0))) t2_2))
                 (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3))
                    (sub (S i0) (Shift (Shift' i0 u0)) t2_3)) =
               tp1
                 (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3))
                    (sub (S i0) (Shift (Shift' i0 u0)) t2_1))
                 (sub (S j0) t (sub (S (S i0)) (Shift (Shift (Shift' i0 u0))) t2_2))
                 (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3))
                    (sub (S i0) (Shift (Shift' i0 u0)) t2_3))) eq_refl
              (Shift (sub i0 (Shift' i0 u0) (Shift' j0 t3)))
              (LP_teq_subst_shift i0 (Shift' i0 u0) (Shift' j0 t3))) (IHt2_1 i0 j0 u0 t3 Hij))
        (IHt2_2 (S i0) (S j0) u0 t3 (le_n_S j0 i0 Hij))) (IHt2_3 i0 j0 u0 t3 Hij))
  (fun (t2_1 : Term)
     (IHt2_1 : forall (i0 j0 : nat) (u0 t3 : Term),
               j0 <= i0 ->
               sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_1) =
               sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_1))
     (t2_2 : Term)
     (IHt2_2 : forall (i0 j0 : nat) (u0 t3 : Term),
               j0 <= i0 ->
               sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_2) =
               sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_2))
     (t2_3 : Term)
     (IHt2_3 : forall (i0 j0 : nat) (u0 t3 : Term),
               j0 <= i0 ->
               sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_3) =
               sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_3))
     (i0 j0 : nat) (u0 t3 : Term) (Hij : j0 <= i0) =>
   eq_ind_r
     (fun t : Term =>
      tp2 (sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_1))
        (sub (S i0) (Shift' (S i0) u0) (sub (S j0) (Shift' (S j0) t3) t2_2)) t =
      tp2 (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_1))
        (sub (S j0) (Shift (sub i0 (Shift' i0 u0) (Shift' j0 t3)))
           (sub (S (S i0)) (Shift' (S (S i0)) u0) t2_2))
        (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_3)))
     (eq_ind_r
        (fun t : Term =>
         tp2 (sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_1)) t
           (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_3)) =
         tp2 (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_1))
           (sub (S j0) (Shift (sub i0 (Shift' i0 u0) (Shift' j0 t3)))
              (sub (S (S i0)) (Shift' (S (S i0)) u0) t2_2))
           (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_3)))
        (eq_ind_r
           (fun t : Term =>
            tp2 t
              (sub (S j0) (sub (S i0) (Shift' (S i0) u0) (Shift' (S j0) t3))
                 (sub (S (S i0)) (Shift' (S (S i0)) u0) t2_2))
              (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_3)) =
            tp2 (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_1))
              (sub (S j0) (Shift (sub i0 (Shift' i0 u0) (Shift' j0 t3)))
                 (sub (S (S i0)) (Shift' (S (S i0)) u0) t2_2))
              (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_3)))
           (eq_ind (sub (S i0) (Shift (Shift' i0 u0)) (Shift (Shift' j0 t3)))
              (fun t : Term =>
               tp2
                 (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3))
                    (sub (S i0) (Shift (Shift' i0 u0)) t2_1))
                 (sub (S j0) (sub (S i0) (Shift (Shift' i0 u0)) (Shift (Shift' j0 t3)))
                    (sub (S (S i0)) (Shift (Shift (Shift' i0 u0))) t2_2))
                 (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3))
                    (sub (S i0) (Shift (Shift' i0 u0)) t2_3)) =
               tp2
                 (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3))
                    (sub (S i0) (Shift (Shift' i0 u0)) t2_1))
                 (sub (S j0) t (sub (S (S i0)) (Shift (Shift (Shift' i0 u0))) t2_2))
                 (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3))
                    (sub (S i0) (Shift (Shift' i0 u0)) t2_3))) eq_refl
              (Shift (sub i0 (Shift' i0 u0) (Shift' j0 t3)))
              (LP_teq_subst_shift i0 (Shift' i0 u0) (Shift' j0 t3))) (IHt2_1 i0 j0 u0 t3 Hij))
        (IHt2_2 (S i0) (S j0) u0 t3 (le_n_S j0 i0 Hij))) (IHt2_3 i0 j0 u0 t3 Hij))
  (fun (t2_1 : Term)
     (IHt2_1 : forall (i0 j0 : nat) (u0 t3 : Term),
               j0 <= i0 ->
               sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_1) =
               sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_1))
     (t2_2 : Term)
     (IHt2_2 : forall (i0 j0 : nat) (u0 t3 : Term),
               j0 <= i0 ->
               sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_2) =
               sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_2))
     (i0 j0 : nat) (u0 t3 : Term) (Hij : j0 <= i0) =>
   eq_ind_r
     (fun t : Term =>
      tsum (sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_1)) t =
      tsum (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_1))
        (sub (S j0) (Shift (sub i0 (Shift' i0 u0) (Shift' j0 t3)))
           (sub (S (S i0)) (Shift' (S (S i0)) u0) t2_2)))
     (eq_ind_r
        (fun t : Term =>
         tsum t
           (sub (S j0) (sub (S i0) (Shift' (S i0) u0) (Shift' (S j0) t3))
              (sub (S (S i0)) (Shift' (S (S i0)) u0) t2_2)) =
         tsum (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_1))
           (sub (S j0) (Shift (sub i0 (Shift' i0 u0) (Shift' j0 t3)))
              (sub (S (S i0)) (Shift' (S (S i0)) u0) t2_2)))
        (eq_ind (sub (S i0) (Shift (Shift' i0 u0)) (Shift (Shift' j0 t3)))
           (fun t : Term =>
            tsum
              (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift (Shift' i0 u0)) t2_1))
              (sub (S j0) (sub (S i0) (Shift (Shift' i0 u0)) (Shift (Shift' j0 t3)))
                 (sub (S (S i0)) (Shift (Shift (Shift' i0 u0))) t2_2)) =
            tsum
              (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift (Shift' i0 u0)) t2_1))
              (sub (S j0) t (sub (S (S i0)) (Shift (Shift (Shift' i0 u0))) t2_2))) eq_refl
           (Shift (sub i0 (Shift' i0 u0) (Shift' j0 t3)))
           (LP_teq_subst_shift i0 (Shift' i0 u0) (Shift' j0 t3))) (IHt2_1 i0 j0 u0 t3 Hij))
     (IHt2_2 (S i0) (S j0) u0 t3 (le_n_S j0 i0 Hij)))
  (fun (t2_1 : Term)
     (IHt2_1 : forall (i0 j0 : nat) (u0 t3 : Term),
               j0 <= i0 ->
               sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_1) =
               sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_1))
     (t2_2 : Term)
     (IHt2_2 : forall (i0 j0 : nat) (u0 t3 : Term),
               j0 <= i0 ->
               sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_2) =
               sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_2))
     (i0 j0 : nat) (u0 t3 : Term) (Hij : j0 <= i0) =>
   eq_ind_r
     (fun t : Term =>
      trefl (sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_1)) t =
      trefl (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_1))
        (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_2)))
     (eq_ind_r
        (fun t : Term =>
         trefl t (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_2)) =
         trefl (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_1))
           (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_2)))
        eq_refl (IHt2_1 i0 j0 u0 t3 Hij)) (IHt2_2 i0 j0 u0 t3 Hij))
  (fun (t2_1 : Term)
     (IHt2_1 : forall (i0 j0 : nat) (u0 t3 : Term),
               j0 <= i0 ->
               sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_1) =
               sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_1))
     (t2_2 : Term)
     (IHt2_2 : forall (i0 j0 : nat) (u0 t3 : Term),
               j0 <= i0 ->
               sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_2) =
               sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_2))
     (t2_3 : Term)
     (IHt2_3 : forall (i0 j0 : nat) (u0 t3 : Term),
               j0 <= i0 ->
               sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_3) =
               sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_3))
     (i0 j0 : nat) (u0 t3 : Term) (Hij : j0 <= i0) =>
   eq_ind_r
     (fun t : Term =>
      teq (sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_1))
        (sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_2)) t =
      teq (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_1))
        (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_2))
        (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_3)))
     (eq_ind_r
        (fun t : Term =>
         teq (sub i0 (Shift' i0 u0) (sub j0 (Shift' j0 t3) t2_1)) t
           (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_3)) =
         teq (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_1))
           (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_2))
           (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_3)))
        (eq_ind_r
           (fun t : Term =>
            teq t (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_2))
              (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_3)) =
            teq (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_1))
              (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_2))
              (sub j0 (sub i0 (Shift' i0 u0) (Shift' j0 t3)) (sub (S i0) (Shift' (S i0) u0) t2_3)))
           eq_refl (IHt2_1 i0 j0 u0 t3 Hij)) (IHt2_2 i0 j0 u0 t3 Hij)) (IHt2_3 i0 j0 u0 t3 Hij)) t2 i
  j u t1
     : forall (i j : nat) (u t1 t2 : Term),
       j <= i ->
       sub i (Shift' i u) (sub j (Shift' j t1) t2) =
       sub j (sub i (Shift' i u) (Shift' j t1)) (sub (S i) (Shift' (S i) u) t2).
