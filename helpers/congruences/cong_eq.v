Definition cong_eq := 
fun (A1 A2 : Type) (u1 v1 : A1) (u2 v2 : A2) (pA : A1 ≅ A2) (pu : u1 ≅ u2) (pv : v1 ≅ v2) =>
match pA with
| @heqPair _ _ _ _ pT pA0 =>
    let pA1 : transport eq_refl A1 = A2 :=
      Logic.eq_ind pT (fun pT0 : Type = Type => transport pT0 A1 = A2) pA0 eq_refl (K pT) in
    match pA1 in (_ = y) return (forall u3 v3 : y, u1 ≅ u3 -> v1 ≅ v3 -> (u1 = v1) ≅ (u3 = v3)) with
    | eq_refl =>
        fun (u3 v3 : A1) (pu0 : u1 ≅ u3) (pv0 : v1 ≅ v3) =>
        match pu0 with
        | @heqPair _ _ _ _ pA2 pu1 =>
            let pu2 : transport eq_refl u1 = u3 :=
              Logic.eq_ind pA2 (fun pA3 : A1 = A1 => transport pA3 u1 = u3) pu1 eq_refl (K pA2) in
            match pu2 in (_ = y) return ((u1 = v1) ≅ (y = v3)) with
            | eq_refl =>
                match pv0 with
                | @heqPair _ _ _ _ pA3 pv1 =>
                    let pv2 : transport eq_refl v1 = v3 :=
                      Logic.eq_ind pA3 (fun pA4 : A1 = A1 => transport pA4 v1 = v3) pv1 eq_refl
                        (K pA3) in
                    match pv2 in (_ = y) return ((u1 = v1) ≅ (u1 = y)) with
                    | eq_refl => heq_refl (u1 = v1)
                    end
                end
            end
        end
    end u2 v2 pu pv
end
     : forall (A1 A2 : Type) (u1 v1 : A1) (u2 v2 : A2),
       A1 ≅ A2 -> u1 ≅ u2 -> v1 ≅ v2 -> (u1 = v1) ≅ (u2 = v2).

