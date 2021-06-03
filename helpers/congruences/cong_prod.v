Definition cong_prod := 
fun (A1 A2 : Type) (B1 : A1 -> Type) (B2 : A2 -> Type) (hA : A1 ≅ A2)
  (hB : forall p : Pack A1 A2, B1 (ProjT1 p) ≅ B2 (ProjT2 p)) =>
heqPair (forall x : A1, B1 x) (forall y : A2, B2 y) eq_refl
  match hA with
  | @heqPair _ _ _ _ pT pA =>
      let pA0 : transport eq_refl A1 = A2 :=
        Logic.eq_ind pT (fun pT0 : Type = Type => transport pT0 A1 = A2) pA eq_refl (K pT) in
      match
        pA0 in (_ = y)
        return
          (forall B3 : y -> Type,
           (forall p : Pack A1 y, B1 (ProjT1 p) ≅ B3 (ProjT2 p)) ->
           (forall x : A1, B1 x) = (forall y0 : y, B3 y0))
      with
      | eq_refl =>
          fun (B3 : A1 -> Type) (hB0 : forall p : Pack A1 A1, B1 (ProjT1 p) ≅ B3 (ProjT2 p)) =>
          let pB : B1 = B3 :=
            funext
              (fun x : A1 =>
               let h :
                 B1 (ProjT1 {| ProjT1 := x; ProjT2 := x; ProjTe := heq_refl x |})
                 ≅ B3 (ProjT2 {| ProjT1 := x; ProjT2 := x; ProjTe := heq_refl x |}) :=
                 hB0 {| ProjT1 := x; ProjT2 := x; ProjTe := heq_refl x |} in
               match h with
               | @heqPair _ _ _ _ pT0 pB =>
                   let pB0 : transport eq_refl (B1 x) = B3 x :=
                     Logic.eq_ind pT0 (fun pT1 : Type = Type => transport pT1 (B1 x) = B3 x) pB
                       eq_refl (K pT0) in
                   pB0
               end) in
          match
            pB in (_ = y)
            return
              ((forall p : Pack A1 A1, B1 (ProjT1 p) ≅ y (ProjT2 p)) ->
               (forall x : A1, B1 x) = (forall y0 : A1, y y0))
          with
          | eq_refl => fun _ : forall p : Pack A1 A1, B1 (ProjT1 p) ≅ B1 (ProjT2 p) => eq_refl
          end hB0
      end B2 hB
  end
     : forall (A1 A2 : Type) (B1 : A1 -> Type) (B2 : A2 -> Type),
       A1 ≅ A2 ->
       (forall p : Pack A1 A2, B1 (ProjT1 p) ≅ B2 (ProjT2 p)) ->
       (forall x : A1, B1 x) ≅ (forall y : A2, B2 y).

