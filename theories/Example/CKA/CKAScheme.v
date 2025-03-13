Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

From NominalSSP Require Import Prelude Group Misc.
Import PackageNotation.
#[local] Open Scope package_scope.

Module CKAscheme.

Record cka_scheme :=
  { Mes : choice_type
  ; Key: choice_type
  ; StateS: choice_type
  ; StateR: choice_type

  ; sampleKey : code fset0 [interface] (Key)
  
  ; keygen : code fset0 [interface] (StateS × StateR)

  ; ckaS : ∀ (state: StateS),
      code fset0 [interface] (StateR × Mes × Key)

  ; ckaR : ∀ (state: StateR) (m : Mes),
      code fset0 [interface] (StateS × Key)
  }.

Notation " 'stateS p " := (StateS p)
  (at level 3) : package_scope.

Notation " 'stateS p " := (StateS p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'stateR p " := (StateR p)
  (at level 3) : package_scope.

Notation " 'stateR p " := (StateR p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'mes p " := (Mes p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'mes p " := (Mes p)
  (at level 3) : package_scope.

Notation " 'key p " := (Key p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'key p " := (Key p)
  (at level 3) : package_scope.

Definition CKAKEY := 0%N.
Definition stater_loc (K: cka_scheme) : Location := ('option ('stateR K); 1%N).
Definition states_loc (K: cka_scheme) : Location := ('option ('stateS K); 2%N).

Definition CKA_loc (K : cka_scheme) :=
  fset [:: stater_loc K ; states_loc K ].

Definition I_CORR_simple (K : cka_scheme) :=
  [interface #val #[ CKAKEY ] : 'unit  → 'unit ].

Definition I_CORR (K : cka_scheme) :=
  [interface #val #[ CKAKEY] : ('nat)  → 'unit ].

Definition CORR0_simple (K : cka_scheme) :
  game (I_CORR_simple K) :=
  [module no_locs ;
    #def #[ CKAKEY ] (_ : 'unit) : 'unit {
      '(pk, x) ← K.(keygen) ;;

      '(stateA, m, kA) ← K.(ckaS) pk ;;
      '(stateB, kB) ← K.(ckaR) x m ;;

      #assert (kA == kB) ;;

      '(stateB', m', kB') ← K.(ckaS) stateB ;;
      '(stateA', kA') ← K.(ckaR) stateA m' ;;

      #assert (kA' == kB') ;;

      @ret 'unit Datatypes.tt
    }
  ].

Definition CORR1_simple (K : cka_scheme) :
  game (I_CORR_simple K) :=
  [module no_locs ;
    #def #[ CKAKEY ] (_: 'unit) : 'unit {
      @ret 'unit Datatypes.tt
    }
  ].

Fixpoint repeat {A : choiceType} (n : nat) (x : A) (c : A → raw_code A) := 
  match n with
   | 0%N => ret x
   | n.+1 => 
      x' ← c x ;;
      repeat n x' c
  end.

Instance valid_repeat:
∀ {A : choiceType} (L : {fset Location}) (I : Interface) (c : A → raw_code A) (x : A) (N : nat),
    (∀ i : A, ValidCode L I (c i)) → ValidCode L I (repeat N x c).
    intros.
    generalize dependent x.
    induction N as [|N IH]; intros x0.
    - simpl. eapply valid_ret.
    - simpl. eapply valid_bind.
      + eapply H.
      + intros x'.
        apply IH.
Qed.

Definition CORR0 (K : cka_scheme) : 
  game (I_CORR K) :=
  [module CKA_loc K ;
    #def #[ CKAKEY ] (n : ('nat)) : 'unit {
      '(pk, x) ← K.(keygen) ;;
      
      repeat (n) ((pk, x) : ('stateS K × 'stateR K))  (fun state =>       
        let '(stateS, stateR) := state in
        '(stateR', m, kS) ← K.(ckaS) stateS ;;
        '(stateS', kR) ← K.(ckaR) stateR m ;;

        #assert (kS == kR) ;;
        @ret ('stateS K × 'stateR K) (stateS', stateR')
      ) ;;
      @ret 'unit Datatypes.tt
    }
  ].
  
Definition CORR1 (K : cka_scheme) :
  game (I_CORR K) :=
  [module no_locs ;
    #def #[ CKAKEY ] (n : 'nat) : 'unit {
      @ret 'unit Datatypes.tt
    }
  ].

Definition CORR K b := if b then CORR0 K else CORR1 K.


Definition INIT := 3%N.
Definition SEND_A := 4%N.
Definition RCV_A := 5%N.
Definition CHALL_A := 6%N.
Definition SEND_B := 7%N.
Definition RCV_B := 8%N.
Definition CHALL_B := 9%N.

Definition I_CKA_PCS (K : cka_scheme) :=
  [interface
    #val #[ INIT ] : 'unit → 'unit ;

    #val #[ SEND_A ] : 'unit → ('mes K × 'key K) ;
    #val #[ RCV_A ] : 'mes K → 'unit;

    #val #[ SEND_B ] : 'unit → ('mes K × 'key K) ;
    #val #[ RCV_B ] : 'mes K → 'unit 
  ].


Definition epoch_a : Location := ('nat; 10%N).
Definition epoch_b : Location := ('nat; 11%N).

Definition state_sa_loc (K: cka_scheme) : Location := ('stateS K; 13%N).
Definition state_sb_loc (K: cka_scheme) : Location := ('stateS K; 14%N).
Definition state_ra_loc (K: cka_scheme) : Location := ('stateR K; 15%N).
Definition state_rb_loc (K: cka_scheme) : Location := ('stateR K; 16%N).

Definition CKA_PCS_locs (K : cka_scheme) :=
  fset [:: state_sa_loc K ; state_sb_loc K ; state_ra_loc K ; state_rb_loc K ; epoch_a ; epoch_b].

Definition CKA_PCS (K : cka_scheme) b t :
  game (I_CKA_PCS K) :=
  [module CKA_PCS_locs K ;
    #def #[ INIT ] (_ : 'unit) : 'unit {
      '(pk, x) ← K.(keygen) ;;

      #put (state_sa_loc K) := pk ;;
      #put (state_sb_loc K) := pk ;;
      #put (state_ra_loc K) := x ;;
      #put (state_rb_loc K) := x ;;

      #put epoch_a := 0 ;;
      #put epoch_b := 0 ;;

      @ret 'unit Datatypes.tt
    } ;

    #def #[ SEND_A ] (_ : 'unit) : ('mes K × 'key K) {
      epoch ← get epoch_a ;;
      let epoch_inc := epoch.+1 in
      #put epoch_a := epoch_inc ;;

      stateSA ← get state_sa_loc K ;;
      '(stateRA, m, k) ← K.(ckaS) stateSA ;;
      #put (state_ra_loc K) := stateRA ;;

      if (t == epoch_inc) && ~~b then
        k' ← K.(sampleKey) ;;
        @ret ('mes K × 'key K) (m, k')
      else
        @ret ('mes K × 'key K) (m, k)
    } ;

    #def #[ RCV_A ] (m : 'mes K) : 'unit {
      epoch ← get epoch_a ;;
      #put epoch_a := epoch.+1 ;;

      stateRA ← get state_ra_loc K ;;
      '(stateSA, k) ← K.(ckaR) stateRA m ;;

      #put (state_sa_loc K) := stateSA ;;

      @ret 'unit Datatypes.tt
    } ;

    #def #[ SEND_B ] (_ : 'unit) : ('mes K × 'key K) {
      epoch ← get epoch_b ;;
      let epoch_inc := epoch.+1 in
      #put epoch_b := epoch.+1 ;;

      stateSB ← get state_sb_loc K ;;
      '(stateRB, m, k) ← K.(ckaS) stateSB ;;

      #put (state_rb_loc K) := stateRB ;;
    
      if (t == epoch_inc) && ~~b then
        k' ← K.(sampleKey) ;;
        @ret ('mes K × 'key K) (m, k')
      else
        @ret ('mes K × 'key K) (m, k)
    } ;

    #def #[ RCV_B ] (m : 'mes K) : 'unit {
      epoch ← get epoch_b ;;
      #put epoch_b := epoch.+1 ;;

      stateRB ← get state_rb_loc K ;;
      '(stateSB, k) ← K.(ckaR) stateRB m ;;

      #put (state_sb_loc K) := stateSB ;;

      @ret 'unit Datatypes.tt
    } 
 ].
  
End CKAscheme.
