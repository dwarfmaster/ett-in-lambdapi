Definition cong_refl := 
fun (A1 A2 : Type) (u1 : A1) (u2 : A2) (pA : A1 ≅ A2) (pu : u1 ≅ u2) =>
match pA with
| @heqPair _ _ _ _ pT pA0 =>
    let pA1 : transport eq_refl A1 = A2 :=
      Logic.eq_ind pT (fun pT0 : Type = Type => transport pT0 A1 = A2) pA0 eq_refl (K pT) in
    match pA1 in (_ = y) return (forall u3 : y, u1 ≅ u3 -> eq_refl ≅ eq_refl) with
    | eq_refl =>
        fun (u3 : A1) (pu0 : u1 ≅ u3) =>
        match pu0 with
        | @heqPair _ _ _ _ pA2 pu1 =>
            let pu2 : transport eq_refl u1 = u3 :=
              Logic.eq_ind pA2 (fun pA3 : A1 = A1 => transport pA3 u1 = u3) pu1 eq_refl (K pA2) in
            match pu2 in (_ = y) return (eq_refl ≅ eq_refl) with
            | eq_refl => heq_refl eq_refl
            end
        end
    end u2 pu
end
     : forall (A1 A2 : Type) (u1 : A1) (u2 : A2), A1 ≅ A2 -> u1 ≅ u2 -> eq_refl ≅ eq_refl.

