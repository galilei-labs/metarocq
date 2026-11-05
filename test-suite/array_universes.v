(* Distributed under the terms of the MIT license. *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import Loader.
From MetaRocq.TemplatePCUIC Require Import TemplateToPCUIC.
From MetaRocq.SafeChecker Require Import
  PCUICSafeChecker PCUICWfEnvImpl PCUICErrors.
From MetaRocq.Erasure.Typed Require Import Erasure.
From MetaRocq.PCUIC Require Import PCUICSN.
From Stdlib Require Import PArray Uint63.

Existing Instance config.extraction_checker_flags.
Existing Instance PCUICSN.extraction_normalizing.
Existing Instance fake_guard_impl_instance.

(* These are the existing extraction normalization/guard assumptions, not new
   axioms for array conversion. No erasure pass is used by this test. *)
Definition array_plain_program (quoted : TemplateProgram.template_program) :=
  let translated := trans_template_program quoted in
  (PCUICProgram.trans_env_env translated.1.1, translated.2).

Definition array_check_program plain_program :=
  typecheck_program canonical_abstract_env_impl
    plain_program Universes.Monomorphic_ctx
    (normalization_in :=
      fun _ _ _ _ _ _ Σ wfΣ _ => @fake_normalization Σ wfΣ)
    (normalization_in' :=
      fun _ _ Σ wfΣ _ => @fake_normalization Σ wfΣ).

Definition array_program_accepted (quoted : TemplateProgram.template_program) : bool :=
  match array_check_program (array_plain_program quoted) with
  | @CorrectDecl _ _ _ => true
  | @EnvError _ _ _ _ => false
  end.

Universe array_u array_v array_w array_x.

Definition array_universe_repro
    (a : array@{array_u} int) : array@{array_v} int := a.

MetaRocq Quote Recursively Definition quoted_array_universe_repro :=
  array_universe_repro.

Example check_array_universe_repro :
  array_program_accepted quoted_array_universe_repro = true.
Proof. vm_compute. reflexivity. Qed.

(* Change only the declared result element type of an otherwise accepted
   quotation. This exercises checker rejection, without disabling Rocq's
   universe checking or relying on an elaborator-side [Fail]. *)
Definition array_element_fixture
    (a : array@{array_u} int) (_ : bool) : array@{array_v} int := a.
MetaRocq Quote Recursively Definition quoted_array_element_fixture :=
  array_element_fixture.

Definition array_modify_type quoted (f : PCUICAst.term -> PCUICAst.term) :=
  let '(Σ, t) := array_plain_program quoted in
  let declarations := map (fun '(kn, d) =>
    match t, d with
    | PCUICAst.tConst target _, PCUICAst.PCUICEnvironment.ConstantDecl cb =>
      if kn == target then
        let ty := f cb.(PCUICAst.PCUICEnvironment.cst_type) in
        (kn, PCUICAst.PCUICEnvironment.ConstantDecl
          {| PCUICAst.PCUICEnvironment.cst_type := ty;
             PCUICAst.PCUICEnvironment.cst_body := cb.(PCUICAst.PCUICEnvironment.cst_body);
             PCUICAst.PCUICEnvironment.cst_universes := cb.(PCUICAst.PCUICEnvironment.cst_universes);
             PCUICAst.PCUICEnvironment.cst_relevance := cb.(PCUICAst.PCUICEnvironment.cst_relevance) |})
      else (kn, d)
    | _, _ => (kn, d)
    end) Σ.(PCUICAst.PCUICEnvironment.declarations) in
  (PCUICAst.PCUICEnvironment.set_declarations Σ declarations, t).

Definition incompatible_array_elements :=
  array_modify_type quoted_array_element_fixture (fun ty =>
    match ty with
    | PCUICAst.tProd na dom (PCUICAst.tProd nb elt (PCUICAst.tApp arr _)) =>
        PCUICAst.tProd na dom
          (PCUICAst.tProd nb elt (PCUICAst.tApp arr elt))
    | ty => ty
    end).

Example check_element_fixture :
  array_program_accepted quoted_array_element_fixture = true.
Proof. vm_compute. reflexivity. Qed.

Polymorphic Definition universe_sensitive@{i} (A : Type@{i}) := (A -> Type@{i})%type.
Definition sensitive_fixture
    (a : universe_sensitive@{array_u} int) (_ : array@{array_v} int) :
    universe_sensitive@{array_u} int := a.
MetaRocq Quote Recursively Definition quoted_sensitive_fixture := sensitive_fixture.

Definition incompatible_sensitive_instances :=
  array_modify_type quoted_sensitive_fixture (fun ty =>
    match ty with
    | PCUICAst.tProd na dom
        (PCUICAst.tProd nb (PCUICAst.tApp (PCUICAst.tConst arr v) elt)
          (PCUICAst.tApp (PCUICAst.tConst sensitive _) elt')) =>
      PCUICAst.tProd na dom
        (PCUICAst.tProd nb (PCUICAst.tApp (PCUICAst.tConst arr v) elt)
          (PCUICAst.tApp (PCUICAst.tConst sensitive v) elt'))
    | ty => ty
    end).

Example check_sensitive_fixture :
  array_program_accepted quoted_sensitive_fixture = true.
Proof. vm_compute. reflexivity. Qed.

Example reject_sensitive_instances :
  match array_check_program incompatible_sensitive_instances with
  | @EnvError _ _ _ (IllFormedDecl _ (NotCumulSmaller _ _ _ _ _ _ _ _ _)) => true
  | _ => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

Example reject_incompatible_array_elements :
  match array_check_program incompatible_array_elements with
  | @EnvError _ _ _ (IllFormedDecl _ (NotCumulSmaller _ _ _ _ _ _ _ _ _)) => true
  | _ => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

Definition overapplied_array_type :=
  array_modify_type quoted_array_element_fixture (fun ty =>
    match ty with
    | PCUICAst.tProd na dom (PCUICAst.tProd nb elt (PCUICAst.tApp arr arg)) =>
      PCUICAst.tProd na dom
        (PCUICAst.tProd nb elt (PCUICAst.tApp (PCUICAst.tApp arr arg) arg))
    | ty => ty
    end).

Example reject_overapplied_array_type :
  match array_check_program overapplied_array_type with
  | @EnvError _ _ _ (IllFormedDecl _ (NotAProduct _ _)) => true
  | _ => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

(* Recognition must follow registration, not the spelling of a constant.
   These direct fixtures also avoid elaborator eta expansion of bare arrays. *)
Module ArrayRegistration.
  Import PCUICAst PCUICEnvironment PCUICEquality PCUICEqualityDec PCUICPosition
    PCUICSafeConversion.

  Definition registered_name : kername :=
    (MPfile ["ArrayRegression"%bs], "deliberately_not_named_array"%bs).
  Definition other_name : kername :=
    (MPfile ["ArrayRegression"%bs], "array"%bs).
  Definition declaration : constant_body :=
    {| cst_type := let s := sType (Universe.make' (Level.lvar 0)) in
         tImpl (tSort s) (tSort s);
       cst_body := None;
       cst_universes := Polymorphic_ctx array_uctx;
       cst_relevance := Relevant |}.
  Definition lookup (_ : kername) : option global_decl :=
    Some (ConstantDecl declaration).

  Definition exact_gate :=
    array_instance_exception_gen lookup (Some registered_name) registered_name
      [Level.lvar 0] [Level.lvar 1].
  Definition one_argument : stack := [App_l (tRel 0)].
  Definition two_arguments : stack := [App_l (tRel 0); App_l (tRel 1)].
  Definition projection_boundary : stack_entry :=
    Proj {| proj_ind := mkInd registered_name 0; proj_npars := 0; proj_arg := 0 |}.

  Example exact_gate_bare : exact_gate [] [] = false.
  Proof. vm_compute. reflexivity. Qed.
  Example exact_gate_saturated : exact_gate one_argument one_argument = true.
  Proof. vm_compute. reflexivity. Qed.
  Example exact_gate_overapplied : exact_gate two_arguments two_arguments = false.
  Proof. vm_compute. reflexivity. Qed.
  Example exact_gate_unequal_spines : exact_gate one_argument two_arguments = false.
  Proof. vm_compute. reflexivity. Qed.
  Example exact_gate_stops_at_projection :
    exact_gate (one_argument ++ projection_boundary :: two_arguments)
      (one_argument ++ projection_boundary :: two_arguments) = true.
  Proof. vm_compute. reflexivity. Qed.
  Example exact_gate_does_not_count_after_projection :
    exact_gate (projection_boundary :: one_argument)
      (projection_boundary :: one_argument) = false.
  Proof. vm_compute. reflexivity. Qed.

  Example registered_arbitrary_name :
    primitive_arrayb_gen lookup (Some registered_name) registered_name = true.
  Proof. vm_compute. reflexivity. Qed.

  Example named_universe_binder :
    primitive_arrayb_gen
      (fun _ => Some (ConstantDecl
        {| cst_type := declaration.(cst_type);
           cst_body := None;
           cst_universes := Polymorphic_ctx ([nNamed "u"%bs], ConstraintSet.empty);
           cst_relevance := Relevant |}))
      (Some registered_name) registered_name = true.
  Proof. vm_compute. reflexivity. Qed.

  Example unregistered_array_name :
    primitive_arrayb_gen lookup None other_name = false.
  Proof. reflexivity. Qed.

  (* Production template translation can add constraints. Recognition checks
     arity; ordinary typing still checks each instance against its constraints. *)
  Example constrained_array_registration (constraints : ConstraintSet.t) :
    primitive_arrayb_gen
      (fun _ => Some (ConstantDecl
        {| cst_type := declaration.(cst_type);
           cst_body := None;
           cst_universes := Polymorphic_ctx ([nNamed "u"%bs], constraints);
           cst_relevance := Relevant |}))
      (Some registered_name) registered_name = true.
  Proof. vm_compute. reflexivity. Qed.

  Example wrong_universe_arity :
    primitive_arrayb_gen
      (fun _ => Some (ConstantDecl
        {| cst_type := declaration.(cst_type);
           cst_body := None;
           cst_universes := Polymorphic_ctx ([nAnon; nAnon], ConstraintSet.empty);
           cst_relevance := Relevant |}))
      (Some registered_name) registered_name = false.
  Proof. vm_compute. reflexivity. Qed.

  Example differently_registered_array_name :
    primitive_arrayb_gen lookup (Some registered_name) other_name = false.
  Proof. vm_compute. reflexivity. Qed.

  Example registration_without_declaration :
    primitive_arrayb_gen (fun _ => None) (Some registered_name) registered_name = false.
  Proof. reflexivity. Qed.

  Example registration_with_body :
    primitive_arrayb_gen
      (fun _ => Some (ConstantDecl
        {| cst_type := declaration.(cst_type);
           cst_body := Some (tRel 0);
           cst_universes := declaration.(cst_universes);
           cst_relevance := Relevant |}))
      (Some registered_name) registered_name = false.
  Proof. vm_compute. reflexivity. Qed.

  Example registration_with_wrong_arity :
    primitive_arrayb_gen
      (fun _ => Some (ConstantDecl
        {| cst_type := tSort Sort.type0;
           cst_body := None;
           cst_universes := declaration.(cst_universes);
           cst_relevance := Relevant |}))
      (Some registered_name) registered_name = false.
  Proof. vm_compute. reflexivity. Qed.

  Example bare_array_sensitive :
    global_variance_gen lookup (Some registered_name) (ConstRef registered_name) 0 = AllEqual.
  Proof. vm_compute. reflexivity. Qed.

  Example saturated_array_irrelevant :
    global_variance_gen lookup (Some registered_name) (ConstRef registered_name) 1 = AllIrrelevant.
  Proof. vm_compute. reflexivity. Qed.

  (* Only the mathematical relation is monotone in surrounding applications.
     The conversion machine must still use Rocq's exact one-argument gate. *)
  Example mathematical_array_monotonicity :
    global_variance_gen lookup (Some registered_name) (ConstRef registered_name) 2 = AllIrrelevant.
  Proof. vm_compute. reflexivity. Qed.

  Definition compare := eqb_term_upto_univ_napp
    (fun _ x y => x == y) (fun _ x y => x == y)
    (compare_global_instance lookup (Some registered_name)
      (fun _ x y => x == y)) Conv 0.

  Example different_instances_same_element :
    compare (tApp (tConst registered_name [Level.lvar 0]) (tRel 0))
            (tApp (tConst registered_name [Level.lvar 1]) (tRel 0)) = true.
  Proof. vm_compute. reflexivity. Qed.

  Example different_instances_bare_constants :
    compare (tConst registered_name [Level.lvar 0])
            (tConst registered_name [Level.lvar 1]) = false.
  Proof. vm_compute. reflexivity. Qed.

  Example different_elements :
    compare (tApp (tConst registered_name [Level.lvar 0]) (tRel 0))
            (tApp (tConst registered_name [Level.lvar 1]) (tRel 1)) = false.
  Proof. vm_compute. reflexivity. Qed.

  Example ordinary_constant_sensitive :
    compare (tApp (tConst other_name [Level.lvar 0]) (tRel 0))
            (tApp (tConst other_name [Level.lvar 1]) (tRel 0)) = false.
  Proof. vm_compute. reflexivity. Qed.

  Example malformed_instance_lengths :
    compare (tApp (tConst registered_name [Level.lvar 0]) (tRel 0))
            (tApp (tConst registered_name []) (tRel 0)) = false.
  Proof. vm_compute. reflexivity. Qed.
End ArrayRegistration.

Definition nested_array_universes
    (a : array@{array_u} (array@{array_v} int)) :
    array@{array_w} (array@{array_x} int) := a.

MetaRocq Quote Recursively Definition quoted_nested_array_universes :=
  nested_array_universes.

Example check_nested_array_universes :
  array_program_accepted quoted_nested_array_universes = true.
Proof. vm_compute. reflexivity. Qed.

Definition equal_array_universes
    (a : array@{array_u} int) : array@{array_u} int := a.

MetaRocq Quote Recursively Definition quoted_equal_array_universes :=
  equal_array_universes.

Example check_equal_array_universes :
  array_program_accepted quoted_equal_array_universes = true.
Proof. vm_compute. reflexivity. Qed.

(* Exercise the extracted production checker too, not only vm_compute. *)
From MetaRocq.SafeCheckerPlugin Require Import Loader.
MetaRocq SafeCheck array_universe_repro.
MetaRocq SafeCheck nested_array_universes.
MetaRocq SafeCheck equal_array_universes.
