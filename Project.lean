--Galois Connections
import Mathlib.Order.FixedPoints
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.GaloisConnection.Defs
import Mathlib.Topology.Order.ScottTopology
import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Data.Set.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Bounds.Defs

--introducing Galois connections
#print LE
#print Preorder
#print Monotone
#print lowerBounds
#print PartialOrder
#print SemilatticeSup
#print SemilatticeInf
#print Lattice
#print CompleteLattice
#print OmegaCompletePartialOrder
#print OmegaCompletePartialOrder.ωScottContinuous  -- a function is ω continuous if it is ScottContinuous over chains
#print GaloisConnection
#print OrderHom
#print ScottContinuous
#print ScottContinuous.monotone
#print IsLUB
#print IsLeast
#print sInf
#print sSup
#print OrderHom.lfp
#print ScottContinuous.ωScottContinuous -- a ScottContinuous function is in particular continuous over chains hence scott-continuous
#print fixedPoints.lfp_eq_sSup_iterate -- Kleene's fixed point is stated in Lean4 for omegacontinuous functions
#print DirectedOn







theorem gal_conn_imply_less_id {α β : Type} [A : CompleteLattice α] [C : CompleteLattice β] (abst : β → α) (concr : α → β )
( h_gal : GaloisConnection abst concr) (a : α)
(b : β) : (abst (concr a) ≤ a) ∧ (b ≤ concr (abst b) )
:= by
        constructor
        case left =>
                    have triv : concr a ≤ concr a := by rfl
                    exact (h_gal (concr a) a).mpr triv
        case right =>
                    have triv : abst b ≤ abst b := by rfl
                    exact (h_gal b (abst b)).mp triv

theorem gal_conn_then_mono {α β : Type} [A : CompleteLattice α] [C : CompleteLattice β] (abst : β → α) (concr : α → β )
( h_gal : GaloisConnection abst concr) : (Monotone abst) ∧ (Monotone concr) := by
    constructor
    case left =>
                 unfold Monotone
                 intro a b hab
                 have aux := (h_gal a (abst b)).mpr
                 have aux' : b ≤ concr (abst b) := by exact (gal_conn_imply_less_id abst concr h_gal ⊥ b).right
                 have aux'' : a ≤ concr (abst b) :=
                              by
                                 calc a
                                 _ ≤ b := by exact hab
                                 _ ≤ _ := by exact aux'
                 exact aux aux''


    case right =>
                  unfold Monotone
                  intro a b hab
                  have aux := (gal_conn_imply_less_id abst concr h_gal a ⊥).left
                  have aux' : abst (concr a) ≤ b :=
                                by
                                    calc abst (concr a)
                                    _ ≤ a := by exact aux
                                    _ ≤ b := by exact hab
                  exact (h_gal (concr a) b).mp aux'



theorem less_id_imply_gal_conn {α β : Type} [A : CompleteLattice α] [C : CompleteLattice β] 
(abst : β → α) (concr : α → β ) (abst_mono : Monotone abst) (concr_mono : Monotone concr) 
(h : (a : α) → (b : β) → ((abst (concr a) ≤ a) ∧ (b ≤ concr (abst b)))) : 
GaloisConnection abst concr :=
        by
            dsimp only [GaloisConnection]
            intro a' b'
            constructor
            case mp =>
              intro h₁
              calc  a'
              _ ≤ concr (abst a') := by exact (h (abst a') a').right
              _ ≤ concr b' := by exact concr_mono h₁
            case mpr =>
              intro h₁
              calc abst a'
              _ ≤ abst (concr b') := by exact abst_mono h₁
              _ ≤ b' := by exact (h b' (concr b')).left

theorem gal_conn_characterization {α β : Type} [A : CompleteLattice α] [C : CompleteLattice β]
{α β : Type} {A : CompleteLattice α} {C : CompleteLattice β} (abst : β → α) (concr : α → β ) (abst_mono : Monotone abst) (concr_mono : Monotone concr) :
(GaloisConnection abst concr) ↔ ((a : α) → (b : β) → ((abst (concr a) ≤ a) ∧ (b ≤ concr (abst b)))) :=
  by
    constructor
    case mp => exact gal_conn_imply_less_id abst concr
    case mpr => exact less_id_imply_gal_conn abst concr abst_mono concr_mono




theorem alpha_determines_gamma {α β : Type} [A : CompleteLattice α] [C : CompleteLattice β] (abst : β → α) (concr : α → β ) (concr' : α → β)
( h_gal : GaloisConnection abst concr) (h_gal' : GaloisConnection abst concr') : concr = concr' := by
  funext a
  have triv₁ : concr a = sSup {s | s ≤ concr a} :=
               by
                  have concr_a_is_ub : (concr a) ∈ upperBounds {s | s ≤ concr a} := by exact mem_upperBounds.mpr (by grind)
                  have concr_a_is_lb_for_ub : (concr a) ∈ lowerBounds (upperBounds {s | s ≤ concr a}) :=
                                      by
                                          dsimp only [lowerBounds]
                                          simp
                                          intro z ip_z
                                          dsimp only [upperBounds] at ip_z
                                          simp at ip_z
                                          exact @ip_z (concr a) (by grind)
                  have h₁ : IsLeast (upperBounds {s | s ≤ concr a}) (concr a) :=
                        by
                           dsimp only [IsLeast]
                           constructor
                           case left => exact concr_a_is_ub
                           case right => exact concr_a_is_lb_for_ub
                  have h₂ : IsLUB {s | s ≤ concr a} (concr a) :=
                        by
                          dsimp only [IsLUB]
                          exact h₁
                  have h₃ := isLUB_iff_sSup_eq.mp h₂
                  rw [h₃]

  have triv₂ : concr' a = sSup {s | s ≤ concr' a} := by sorry
  have galcons₁ :   {s | s ≤ concr a} =  {s | abst s ≤ a} :=
                  by
                     ext x
                     simp
                     have auxx := h_gal x a
                     grind
  have galcons₂ : {s | s ≤ concr' a} = {s | abst s ≤ a} :=
                  by
                    ext x
                    simp
                    have auxx := h_gal' x a
                    grind
  grind





-- introducing correct approximations

def CorrectApproximation {α β : Type} [A : CompleteLattice α] [C : CompleteLattice β]
(abst : β → α) (concr : α → β )
( h_gal : GaloisConnection abst concr) (g : α → α) (f : β → β) : Prop
:=  (b : β) → (f b ≤ concr (g (abst b)))

theorem CorrectApproximationProperty {α β : Type} [A : CompleteLattice α] [C : CompleteLattice β] (abst : β → α) 
(concr : α → β ) 
( h_gal : GaloisConnection abst concr) (g : α →o α)
(f : β →o β) : (CorrectApproximation abst concr h_gal g f) ↔ ((a : α) → (abst (f (concr a)) ≤ (g a))) := by
      constructor
      case mp =>
        intro h
        have obs : ∀ c : β, abst (f c) ≤ g (abst c) :=
                by
                    intro c'
                    have aux :=  h c'
                    exact (h_gal (f c') (g (abst c'))).mpr aux
        intro a
        have aux' := (h_gal (concr a) a).mpr
        have triv : concr a ≤ concr a := by rfl
        have aux'' := aux' triv
        calc abst (f (concr a))
          _ ≤ g (abst (concr a)) := obs (concr a)
          _ ≤ g a := by exact g.mono aux''



      case mpr =>
        intro h
        unfold CorrectApproximation
        intro b
        have triv : abst b ≤ abst b := by rfl
        have aux := (h_gal b (abst b)).mp triv
        have aux' := (h_gal ( f (concr (abst b))) (g (abst b))).mp (h (abst b))
        calc f b
          _ ≤ f (concr (abst b)) := f.mono aux
          _ ≤ _ := by exact aux'



-- final result

#print Nat.iterate

theorem iterate_property {α : Type} (n: Nat) (f : α → α) (a : α) : f^[n] (f a) = f (f^[n] a) := by
                    revert a
                    induction n
                    case zero => simp
                    case succ k ik =>
                                        simp
                                        intro a'
                                        rw [ik (f a')]
-- I need this to exploit the monotonicity of the underlying function of f



theorem IterateInfPropertyLemma {α : Type} [L : CompleteLattice α] :
                    (f : α →o α) → (n : Nat) →  (⇑f)^[n] ⊥ ≤ (⇑f)^[n + 1] ⊥
      := by
        intro f n
        induction n
        case zero => simp
        case succ k ik =>
                          simp
                          simp at ik
                          rw [iterate_property k f ⊥] at ik
                          rw [iterate_property k f (f ⊥)]
                          rw [iterate_property]
                          exact f.mono ik





theorem IterateInfProperty {α : Type} [L : CompleteLattice α] :
    (f : α →o α) → (n m : Nat) → (n ≤ m) →  (⇑f)^[n] ⊥ ≤ (⇑f)^[m] ⊥
      := by
      intro f n m h
      induction h
      case refl => rfl
      case step m a i_a =>
                            calc (⇑f)^[n] ⊥
                              _ ≤ (⇑f)^[m] ⊥ := by exact i_a
                              _ ≤ (⇑f)^[m.succ] ⊥ := by exact IterateInfPropertyLemma f m


theorem maintheorem {α β : Type} [A : CompleteLattice α] [C : CompleteLattice β] (f : β →o β) (g : α →o α) 
(f_cont : ScottContinuous f) (g_cont : ScottContinuous g)
(abst : β → α) (concr : α → β ) ( h_gal : GaloisConnection abst concr)
(h_corr_approx : CorrectApproximation abst concr h_gal g f)
(concr_continuous : ScottContinuous concr)
:
OrderHom.lfp f  ≤ concr (OrderHom.lfp g)
:= by
     rw [fixedPoints.lfp_eq_sSup_iterate f (ScottContinuous.ωScottContinuous f_cont)]
     rw [fixedPoints.lfp_eq_sSup_iterate g (ScottContinuous.ωScottContinuous g_cont)]


     -- I have to prove that the interestd set is direct in order to rewrite the inequality using scott continuity
     have direct : DirectedOn LE.le {x | ∃ n : Nat, (⇑g)^[n] ⊥ = x} :=
                  by
                      unfold DirectedOn
                      intro x def_x y def_y
                      simp at def_x
                      simp at def_y
                      have ⟨n_x, def_n_x ⟩ := def_x
                      have ⟨ n_y, def_n_y ⟩ := def_y

                      exists  (⇑g)^[n_x + n_y] ⊥
                      constructor
                      case right =>
                        constructor
                        case left =>
                                    rw [← def_n_x]
                                    have triv : n_x ≤ n_x + n_y := by grind
                                    exact IterateInfProperty g n_x (n_x + n_y) (triv)
                        case right =>
                                   rw [← def_n_y]
                                   have triv : n_y ≤ n_x + n_y := by grind
                                   exact IterateInfProperty g n_y (n_x + n_y) (triv)

                      case left =>
                                    simp
     have notempty : {x | ∃ n : Nat, (⇑g)^[n] ⊥ = x}.Nonempty :=
                      by
                        exists ⊥
                        simp
                        exists 0
     -- ScottContinuity is expressed in terms of the IsLUB proposition in Lean

     have argIsSup : ⨆ n, (⇑g)^[n] ⊥ = sSup {x | ∃ n, (⇑g)^[n] ⊥ = x} :=
                    by
                         rw [sSup_eq_iSup]
                         exact Eq.symm iSup_range -- used exact?



     have argIsLUB :  IsLUB {x | ∃ n, (⇑g)^[n] ⊥ = x} (⨆ n, (⇑g)^[n] ⊥) :=
                    by
                        rw [argIsSup]
                        exact CompleteLattice.isLUB_sSup {x | ∃ n, (⇑g)^[n] ⊥ = x}
     -- here we exploit the fact that concr is a continuous function
     have cont_application : concr (⨆ n, (⇑g)^[n] ⊥) = ⨆ n, concr ((⇑g)^[n] ⊥) :=
                            by
                                have aux : IsLUB (concr '' {x | ∃ n, (⇑g)^[n] ⊥ = x}) (concr (⨆ n, (⇑g)^[n] ⊥))  :=  by exact concr_continuous notempty direct argIsLUB


                                have def_im : (concr '' {x | ∃ n, (⇑g)^[n] ⊥ = x}) = {x | ∃ n, concr ((⇑g)^[n] ⊥) = x} := by grind
                                rw [def_im] at aux
                                have aux' := isLUB_iff_sSup_eq.mp aux
                                rw [← aux']
                                rw [sSup_eq_iSup]
                                exact iSup_range -- automation used (exact ?)



     rw [cont_application]
     
     have fund_ineq : ∀ n : Nat, (⇑f)^[n] ⊥ ≤ concr ((⇑g)^[n] ⊥) :=
                      by
                          intro k
                          induction k
                          case zero => simp
                          case succ s is =>
                                        unfold Nat.iterate
                                        rw [iterate_property s ⇑f ⊥, iterate_property s ⇑g ⊥]
                                        have ineq₂  : concr (abst (f (concr ((⇑g)^[s] ⊥))))≤ concr (g ((⇑g)^[s] ⊥)) :=
                                                      by
                                                        have aux : abst (f (concr ((⇑g)^[s] ⊥))) ≤ g ((⇑g)^[s] ⊥) :=
                                                                    by
                                                                      exact (CorrectApproximationProperty abst concr h_gal g f).mp h_corr_approx ((⇑g)^[s] ⊥)
                                                        exact (gal_conn_then_mono abst concr h_gal).2 aux
                                        have ineq₁ : f (concr (g^[s] ⊥)) ≤ concr (abst (f (concr ((⇑g)^[s] ⊥)))) := by exact (gal_conn_imply_less_id abst concr h_gal ⊥ (f (concr (g^[s] ⊥)))).2

                                        have ineq₀ : f (f^[s] ⊥) ≤ f (concr (g^[s] ⊥)) :=
                                                    by
                                                      exact f.monotone is

                                        calc  f ((⇑f)^[s] ⊥)
                                          _ ≤ f (concr (g^[s] ⊥)) := by  exact ineq₀
                                          _ ≤ concr (abst (f (concr ((⇑g)^[s] ⊥)))) := by exact ineq₁
                                          _ ≤ concr (g ((⇑g)^[s] ⊥)) := by exact ineq₂




    
     dsimp only [iSup]
     let x := (Set.range fun n ↦ (⇑f)^[n] ⊥)
     let y := (Set.range fun n ↦ concr ((⇑g)^[n] ⊥))
     --have set_y_bddabove : BddAbove y := by simp
     have sup_x_lt_ub : ∀ b ∈ upperBounds y, sSup x ≤ b :=
            by
              intro b b_ub
              dsimp only [upperBounds] at b_ub
              simp at b_ub
              have cor_lt :  ∀ ⦃c : β⦄, c ∈ x → c ≤ b :=
                            by
                              intro c def_c
                              dsimp only [x] at def_c
                              simp at def_c
                              have ⟨ z , def_z ⟩ := def_c

                              have comparison : (⇑f)^[z] ⊥ ≤ concr ((⇑g)^[z] ⊥) := by exact fund_ineq z
                              have comparison' : concr ((⇑g)^[z] ⊥) ≤ b := by grind -- b is an upperbound for why and concr ( g ^ z ⊥) is in y
                              grind
                                                                -- now let's show that b is an upper bound for x
              have b_ub_for_x_too : b ∈ upperBounds x := by exact mem_upperBounds.mpr cor_lt
              exact sSup_le b_ub_for_x_too








     have conclusion : sSup x ≤ sSup y := by
                                                have triv : sSup y ∈ upperBounds y := by
                                                                                          unfold upperBounds
                                                                                          simp
                                                                                          intro a h_a
                                                                                          exact le_sSup h_a
                                                exact sup_x_lt_ub (sSup y) triv



     dsimp only [x, y] at conclusion
     exact conclusion
