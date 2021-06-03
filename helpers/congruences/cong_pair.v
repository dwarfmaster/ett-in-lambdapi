Definition cong_pair := 
fun (A1 A2 : Type) (B1 : A1 -> Type) (B2 : A2 -> Type) (u1 : A1) (u2 : A2) 
  (v1 : B1 u1) (v2 : B2 u2) (hA : A1 ≅ A2) (hB : forall p : Pack A1 A2, B1 (ProjT1 p) ≅ B2 (ProjT2 p))
  (hu : u1 ≅ u2) (hv : v1 ≅ v2) =>
match hA with
| @heqPair _ _ _ _ pT pA =>
    let pA0 : transport eq_refl A1 = A2 :=
      Logic.eq_ind pT (fun pT0 : Type = Type => transport pT0 A1 = A2) pA eq_refl (K pT) in
    match
      pA0 in (_ = y)
      return
        (forall (B3 : y -> Type) (u3 : y) (v3 : B3 u3),
         (forall p : Pack A1 y, B1 (ProjT1 p) ≅ B3 (ProjT2 p)) ->
         u1 ≅ u3 -> v1 ≅ v3 -> epair u1 v1 ≅ epair u3 v3)
    with
    | eq_refl =>
        fun (B3 : A1 -> Type) (u3 : A1) (v3 : B3 u3)
          (hB0 : forall p : Pack A1 A1, B1 (ProjT1 p) ≅ B3 (ProjT2 p)) (hu0 : u1 ≅ u3) 
          (hv0 : v1 ≅ v3) =>
        let pB : B1 = B3 :=
          funext
            (fun x : A1 =>
             let h :
               B1 (ProjT1 {| ProjT1 := x; ProjT2 := x; ProjTe := heq_refl x |})
               ≅ B3 (ProjT2 {| ProjT1 := x; ProjT2 := x; ProjTe := heq_refl x |}) :=
               hB0 {| ProjT1 := x; ProjT2 := x; ProjTe := heq_refl x |} in
             match h with
             | @heqPair _ _ _ _ pT0 pB =>
                 let pB0 :
                   transport eq_refl
                     (B1 (ProjT1 {| ProjT1 := x; ProjT2 := x; ProjTe := heq_refl x |})) =
                   B3 (ProjT2 {| ProjT1 := x; ProjT2 := x; ProjTe := heq_refl x |}) :=
                   Logic.eq_ind pT0
                     (fun pT1 : Type = Type =>
                      transport pT1 (B1 (ProjT1 {| ProjT1 := x; ProjT2 := x; ProjTe := heq_refl x |})) =
                      B3 (ProjT2 {| ProjT1 := x; ProjT2 := x; ProjTe := heq_refl x |})) pB eq_refl
                     (K pT0) in
                 pB0
             end) in
        match
          pB in (_ = y)
          return
            (forall v4 : y u3,
             (forall p : Pack A1 A1, B1 (ProjT1 p) ≅ y (ProjT2 p)) ->
             v1 ≅ v4 -> epair u1 v1 ≅ epair u3 v4)
        with
        | eq_refl =>
            fun (v4 : B1 u3) (_ : forall p : Pack A1 A1, B1 (ProjT1 p) ≅ B1 (ProjT2 p))
              (hv1 : v1 ≅ v4) =>
            match hu0 with
            | @heqPair _ _ _ _ pT0 pu =>
                let pu0 : transport eq_refl u1 = u3 :=
                  Logic.eq_ind pT0 (fun pT1 : A1 = A1 => transport pT1 u1 = u3) pu eq_refl (K pT0) in
                match
                  pu0 in (_ = y) return (forall v5 : B1 y, v1 ≅ v5 -> epair u1 v1 ≅ epair y v5)
                with
                | eq_refl =>
                    fun (v5 : B1 u1) (hv2 : v1 ≅ v5) =>
                    match hv2 with
                    | @heqPair _ _ _ _ pT1 pv =>
                        let pv0 : transport eq_refl v1 = v5 :=
                          Logic.eq_ind pT1 (fun pT2 : B1 u1 = B1 u1 => transport pT2 v1 = v5) pv
                            eq_refl (K pT1) in
                        match pv0 in (_ = y) return (epair u1 v1 ≅ epair u1 y) with
                        | eq_refl => heq_refl (epair u1 v1)
                        end
                    end
                end v4 hv1
            end
        end v3 hB0 hv0
    end B2 u2 v2 hB hu hv
end
     : forall (A1 A2 : Type) (B1 : A1 -> Type) (B2 : A2 -> Type) (u1 : A1) 
         (u2 : A2) (v1 : B1 u1) (v2 : B2 u2),
       A1 ≅ A2 ->
       (forall p : Pack A1 A2, B1 (ProjT1 p) ≅ B2 (ProjT2 p)) ->
       u1 ≅ u2 -> v1 ≅ v2 -> epair u1 v1 ≅ epair u2 v2.

