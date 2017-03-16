(*
(** * Records: Adding Records to STLC *)
*)
(** * Records: STLCにレコードを追加する *)

Require Export Stlc.

(* ###################################################################### *)
(*
(** * Adding Records *)
*)
(** * レコードを追加する *)

(*
(** We saw in chapter [MoreStlc] how records can be treated as syntactic
    sugar for nested uses of products.  This is fine for simple
    examples, but the encoding is informal (in reality, if we really
    treated records this way, it would be carried out in the parser,
    which we are eliding here), and anyway it is not very efficient.
    So it is also interesting to see how records can be treated as
    first-class citizens of the language. 

    Recall the informal definitions we gave before: *)
*)
(** [MoreStlc]章で、レコードを、直積のネストされた使用の構文糖衣として扱う方法を見ました。
    これは簡単な例にはよいです。
    しかし、エンコードは非形式的です。
    (現実的に、もしこの方法でレコードを本当に扱うならパーサ内で実行されることになりますが、
    パーサはここでは省いています。)
    そしていずれにしろ、あまり効率的ではありません。
    これから、レコードを言語の第一級(first-class)のメンバーとしてはどのように扱えるのか見るのも興味があるところです。
 
    前の非形式的定義を思い出してみましょう: *)

(*
(**
    Syntax:
<<
       t ::=                          Terms:
           | ...
           | {i1=t1, ..., in=tn}         record 
           | t.i                         projection

       v ::=                          Values:
           | ...
           | {i1=v1, ..., in=vn}         record value

       T ::=                          Types:
           | ...
           | {i1:T1, ..., in:Tn}         record type
>> 
   Reduction:
                                 ti ==> ti'                            (ST_Rcd)
    --------------------------------------------------------------------  
    {i1=v1, ..., im=vm, in=tn, ...} ==> {i1=v1, ..., im=vm, in=tn', ...}

                                 t1 ==> t1'
                               --------------                        (ST_Proj1)
                               t1.i ==> t1'.i

                          -------------------------                (ST_ProjRcd)
                          {..., i=vi, ...}.i ==> vi
   Typing:
               Gamma |- t1 : T1     ...     Gamma |- tn : Tn
             --------------------------------------------------         (T_Rcd)
             Gamma |- {i1=t1, ..., in=tn} : {i1:T1, ..., in:Tn}

                       Gamma |- t : {..., i:Ti, ...}
                       -----------------------------                   (T_Proj)
                             Gamma |- t.i : Ti
*)
*)
(**
    構文:
<<
       t ::=                          項:
           | ... 
           | {i1=t1, ..., in=tn}         レコード
           | t.i                         射影
 
       v ::=                          値:
           | ... 
           | {i1=v1, ..., in=vn}         レコード値
 
       T ::=                          型:
           | ... 
           | {i1:T1, ..., in:Tn}         レコード型
>>
   簡約:
[[
                                 ti ==> ti'                            (ST_Rcd) 
    -------------------------------------------------------------------- 
    {i1=v1, ..., im=vm, in=tn, ...} ==> {i1=v1, ..., im=vm, in=tn', ...} 
 
                                 t1 ==> t1' 
                               --------------                        (ST_Proj1) 
                               t1.i ==> t1'.i 
 
                          -------------------------                (ST_ProjRcd) 
                          {..., i=vi, ...}.i ==> vi 
]]
   型付け:
[[
               Gamma |- t1 : T1     ...     Gamma |- tn : Tn 
             --------------------------------------------------         (T_Rcd) 
             Gamma |- {i1=t1, ..., in=tn} : {i1:T1, ..., in:Tn} 
 
                       Gamma |- t : {..., i:Ti, ...} 
                       -----------------------------                   (T_Proj) 
                             Gamma |- t.i : Ti 
]]
*)

(* ###################################################################### *)
(*
(** * Formalizing Records *)
*)
(** * レコードを形式化する *)

Module STLCExtendedRecords.

(* ###################################################################### *)
(*
(** *** Syntax and Operational Semantics *)
*)
(** *** 構文と操作的意味 *)

(*
(** The most obvious way to formalize the syntax of record types would
    be this: *)
*)
(** レコード型の構文を形式化する最も明らかな方法はこうです: *)

Module FirstTry.

Definition alist (X : Type) := list (id * X).
  
Inductive ty : Type :=
  | TBase     : id -> ty
  | TArrow    : ty -> ty -> ty
  | TRcd      : (alist ty) -> ty.

(*
(** Unfortunately, we encounter here a limitation in Coq: this type
    does not automatically give us the induction principle we expect
    -- the induction hypothesis in the [TRcd] case doesn't give us
    any information about the [ty] elements of the list, making it
    useless for the proofs we want to do.  *)
*)
(** 残念ながら、ここで Coq の限界につきあたりました。
    この型は期待する帰納原理を自動的には提供してくれないのです。
    [TRcd]の場合の帰納法の仮定はリストの[ty]要素について何の情報も提供してくれないのです。
    このせいで、行いたい証明に対してこの型は役に立たなくなっています。 *)

(* Check ty_ind. 
   ====>
    ty_ind : 
      forall P : ty -> Prop,
        (forall i : id, P (TBase i)) ->
        (forall t : ty, P t -> forall t0 : ty, P t0 -> P (TArrow t t0)) ->
        (forall a : alist ty, P (TRcd a)) ->    (* ??? *)
        forall t : ty, P t
*)
(** <<
(* Check ty_ind. 
   ====> 
    ty_ind : 
      forall P : ty -> Prop, 
        (forall i : id, P (TBase i)) -> 
        (forall t : ty, P t -> forall t0 : ty, P t0 -> P (TArrow t t0)) -> 
        (forall a : alist ty, P (TRcd a)) ->    (* ??? *) 
        forall t : ty, P t 
*) 
>> *)

End FirstTry.

(*
(** It is possible to get a better induction principle out of Coq, but
    the details of how this is done are not very pretty, and it is not
    as intuitive to use as the ones Coq generates automatically for
    simple [Inductive] definitions.

    Fortunately, there is a different way of formalizing records that
    is, in some ways, even simpler and more natural: instead of using
    the existing [list] type, we can essentially include its
    constructors ("nil" and "cons") in the syntax of types. *)
*)
(** より良い帰納法の原理をCoqから取り出すこともできます。
    しかしそれをやるための詳細はあまりきれいではありません。
    またCoqが単純な[Inductive]定義に対して自動生成したものほど直観的でもありません。
 
    幸い、レコードについて、別の、ある意味より単純でより自然な形式化方法があります。
    既存の[list]型の代わりに、型の構文にリストのコンストラクタ("nil"と"cons")
    を本質的に含めてしまうという方法です。*)

Inductive ty : Type :=
  | TBase : id -> ty
  | TArrow : ty -> ty -> ty
  | TRNil : ty
  | TRCons : id -> ty -> ty -> ty.

Tactic Notation "T_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "TBase" | Case_aux c "TArrow"
  | Case_aux c "TRNil" | Case_aux c "TRCons" ].

(*
(** Similarly, at the level of terms, we have constructors [trnil]
    -- the empty record -- and [trcons], which adds a single field to
    the front of a list of fields. *)
*)
(** 同様に、項のレベルで、空レコードに対応するコンストラクタ[trnil]と、
    フィールドのリストの前に1つのフィールドを追加するコンストラクタ[trcons]を用意します。*)

Inductive tm : Type :=
  | tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : id -> ty -> tm -> tm
  (* records *)
  (** <<
  (* レコード *)
>> *)
  | tproj : tm -> id -> tm
  | trnil :  tm
  | trcons : id -> tm -> tm -> tm.

Tactic Notation "t_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tvar" | Case_aux c "tapp" | Case_aux c "tabs"
  | Case_aux c "tproj" | Case_aux c "trnil" | Case_aux c "trcons" ].

(*
(** Some variables, for examples... *)
*)
(** いくつかの変数、例えば... *)

Notation a := (Id 0).
Notation f := (Id 1).
Notation g := (Id 2).
Notation l := (Id 3).
Notation A := (TBase (Id 4)).
Notation B := (TBase (Id 5)).
Notation k := (Id 6).
Notation i1 := (Id 7).
Notation i2 := (Id 8).

(** [{ i1:A }] *)

(* Check (TRCons i1 A TRNil). *)
(** <<
(* Check (TRCons i1 A TRNil). *) 
>> *)

(** [{ i1:A->B, i2:A }] *)

(* Check (TRCons i1 (TArrow A B) 
           (TRCons i2 A TRNil)). *)
(** <<
(* Check (TRCons i1 (TArrow A B)
           (TRCons i2 A TRNil)). *) 
>> *)

(* ###################################################################### *)
(*
(** *** Well-Formedness *)
*)
(** *** Well-Formedness(正しい形をしていること、整式性) *)

(*
(** Generalizing our abstract syntax for records (from lists to the
    nil/cons presentation) introduces the possibility of writing
    strange types like this *)
*)
(** レコードの抽象構文を(リストから nil/cons 構成に)一般化すると、
    次のような奇妙な型を書くことがができるようになります。 *)

Definition weird_type := TRCons X A B.

(*
(** where the "tail" of a record type is not actually a record type! *)
*)
(** ここでレコード型の「後部」は実際にはレコード型ではありません! *)

(*
(** We'll structure our typing judgement so that no ill-formed types
    like [weird_type] are assigned to terms.  To support this, we
    define [record_ty] and [record_tm], which identify record types
    and terms, and [well_formed_ty] which rules out the ill-formed
    types. *)
*)
(** 以降で型ジャッジメントを、
    [weird_type]のようなill-formedの(正しくない形の)型が項に割当てられないように構成します。
    これをサポートするために、レコード型と項を識別するための[record_ty]と[record_tm]、
    およびill-formedの型を排除するための[well_formed_ty]を定義します。*)

(*
(** First, a type is a record type if it is built with just [TRNil]
    and [TRCons] at the outermost level. *)
*)
(** 最初に、型がレコード型なのは、
    それの一番外側のレベルが[TRNil]と[TRCons]だけを使って構築されたもののときです。*)

Inductive record_ty : ty -> Prop :=
  | RTnil : 
        record_ty TRNil
  | RTcons : forall i T1 T2,
        record_ty (TRCons i T1 T2).

(*
(** Similarly, a term is a record term if it is built with [trnil]
    and [trcons] *)
*)
(** 同様に、項がレコード項であるのは、
    [trnil]と[trcons]から構築されたもののときです。 *)

Inductive record_tm : tm -> Prop :=
  | rtnil :
        record_tm trnil
  | rtcons : forall i t1 t2,
        record_tm (trcons i t1 t2).

(*
(** Note that [record_ty] and [record_tm] are not recursive -- they
    just check the outermost constructor.  The [well_formed_ty]
    property, on the other hand, verifies that the whole type is well
    formed in the sense that the tail of every record (the second
    argument to [TRCons]) is a record.

    Of course, we should also be concerned about ill-formed terms, not
    just types; but typechecking can rules those out without the help
    of an extra [well_formed_tm] definition because it already
    examines the structure of terms.  *)
*)
(** [record_ty]と[record_tm]は再帰的ではないことに注意します。
    両者は、一番外側のコンストラクタだけをチェックします。
    一方[well_formed_ty]は型全体がwell-formedか(正しい形をしているか)、
    つまり、レコードのすべての後部([TRCons]の第2引数)がレコードであるか、を検証します。
 
    もちろん、型だけでなく項についても、ill-formedの可能性を考慮しなければなりません。
    しかし、別途[well_formed_tm]を用意しなくても、ill-formed項は型チェックが排除します。
    なぜなら、型チェックが既に項の構成を調べるからです。*)    
(** LATER : should they fill in part of this as an exercise?  We
    didn't give rules for it above *)
(** (訳注：この"LATER"部分が誰向けに何を言おうとしているのかはっきりしないので、
    訳さずに残しておきました。) *)

Inductive well_formed_ty : ty -> Prop :=
  | wfTBase : forall i,
        well_formed_ty (TBase i)
  | wfTArrow : forall T1 T2,
        well_formed_ty T1 ->
        well_formed_ty T2 ->
        well_formed_ty (TArrow T1 T2)
  | wfTRNil :
        well_formed_ty TRNil
  | wfTRCons : forall i T1 T2,
        well_formed_ty T1 ->
        well_formed_ty T2 ->
        record_ty T2 ->
        well_formed_ty (TRCons i T1 T2).

Hint Constructors record_ty record_tm well_formed_ty.

(* ###################################################################### *)
(*
(** *** Substitution *)
*)
(** *** 置換 *)

Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | tvar y => if eq_id_dec x y then s else t
  | tabs y T t1 =>  tabs y T (if eq_id_dec x y then t1 else (subst x s t1))
  | tapp t1 t2 => tapp (subst x s t1) (subst x s t2)
  | tproj t1 i => tproj (subst x s t1) i
  | trnil => trnil
  | trcons i t1 tr1 => trcons i (subst x s t1) (subst x s tr1)
  end.

Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).

(* ###################################################################### *)
(*
(** *** Reduction *)
*)
(** *** 簡約 *)

(*
(** Next we define the values of our language.  A record is a value if
    all of its fields are. *)
*)
(** 次に言語の値を定義します。レコードが値であるのは、そのフィールドがすべて値であるときです。*)

Inductive value : tm -> Prop :=
  | v_abs : forall x T11 t12,
      value (tabs x T11 t12)
  | v_rnil : value trnil
  | v_rcons : forall i v1 vr,
      value v1 ->
      value vr ->
      value (trcons i v1 vr).

Hint Constructors value.

(*
(** Utility functions for extracting one field from record type or
    term: *)
*)
(** レコード型またはレコード項から1つのフィールドを取り出すユーティリティ関数です: *)

Fixpoint Tlookup (i:id) (Tr:ty) : option ty :=
  match Tr with
  | TRCons i' T Tr' => if eq_id_dec i i' then Some T else Tlookup i Tr'
  | _ => None
  end.

Fixpoint tlookup (i:id) (tr:tm) : option tm :=
  match tr with
  | trcons i' t tr' => if eq_id_dec i i' then Some t else tlookup i tr'
  | _ => None
  end.

(*
(** The [step] function uses the term-level lookup function (for the
    projection rule), while the type-level lookup is needed for
    [has_type]. *)
*)
(** [step]関数は(射影規則について)項レベルのlookup関数を使います。
    一方、型レベルのlookupは[has_type]で必要になります。*)

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T11 t12 v2,
         value v2 ->
         (tapp (tabs x T11 t12) v2) ==> ([x:=v2]t12)
  | ST_App1 : forall t1 t1' t2,
         t1 ==> t1' ->
         (tapp t1 t2) ==> (tapp t1' t2)
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 ==> t2' ->
         (tapp v1 t2) ==> (tapp v1 t2')
  | ST_Proj1 : forall t1 t1' i,
        t1 ==> t1' ->
        (tproj t1 i) ==> (tproj t1' i)
  | ST_ProjRcd : forall tr i vi,
        value tr ->
        tlookup i tr = Some vi ->
        (tproj tr i) ==> vi
  | ST_Rcd_Head : forall i t1 t1' tr2,
        t1 ==> t1' ->
        (trcons i t1 tr2) ==> (trcons i t1' tr2)
  | ST_Rcd_Tail : forall i v1 tr2 tr2',
        value v1 ->
        tr2 ==> tr2' ->
        (trcons i v1 tr2) ==> (trcons i v1 tr2')

where "t1 '==>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_AppAbs" | Case_aux c "ST_App1" | Case_aux c "ST_App2"
  | Case_aux c "ST_Proj1" | Case_aux c "ST_ProjRcd"
  | Case_aux c "ST_Rcd_Head" | Case_aux c "ST_Rcd_Tail" ].

Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

Hint Constructors step.

(* ###################################################################### *)
(*
(** *** Typing *)
*)
(** *** 型付け *)

Definition context := partial_map ty.

(*
(** Next we define the typing rules.  These are nearly direct
    transcriptions of the inference rules shown above.  The only major
    difference is the use of [well_formed_ty].  In the informal
    presentation we used a grammar that only allowed well formed
    record types, so we didn't have to add a separate check.

    We'd like to set things up so that that whenever [has_type Gamma t
    T] holds, we also have [well_formed_ty T].  That is, [has_type]
    never assigns ill-formed types to terms.  In fact, we prove this
    theorem below.

    However, we don't want to clutter the definition of [has_type]
    with unnecessary uses of [well_formed_ty].  Instead, we place
    [well_formed_ty] checks only where needed - where an inductive
    call to [has_type] won't already be checking the well-formedness
    of a type.

    For example, we check [well_formed_ty T] in the [T_Var] case,
    because there is no inductive [has_type] call that would 
    enforce this.  Similarly, in the [T_Abs] case, we require a
    proof of [well_formed_ty T11] because the inductive call to
    [has_type] only guarantees that [T12] is well-formed.

    In the rules you must write, the only necessary [well_formed_ty]
    check comes in the [tnil] case.  *)
*)
(** 次に型付け規則を定義します。これは上述の推論規則をほぼそのまま転写したものです。
    大きな違いは[well_formed_ty]の使用だけです。
    非形式的な表記では、well-formedレコード型だけを許す文法を使ったので、
    別のチェックを用意する必要はありませんでした。
 
    ここでは、[has_type Gamma t T] が成立するときは常に [well_formed_ty T] 
    が成立するようにしたいところです。つまり、[has_type] 
    は項にill-formed型を割当てることはないようにするということです。
    このことを後で実際に証明します。
 
    しかしながら[has_type]の定義を、[well_formed_ty]
    を不必要に使って取り散らかしたくはありません。
    その代わり[well_formed_ty]によるチェックを必要な所だけに配置します。
    ここで、必要な所というのは、[has_type]
    の帰納的呼び出しによっても未だ型のwell-formed性のチェックが行われていない所のことです。
 
    例えば、[T_Var]の場合、[well_formed_ty T] をチェックします。
    なぜなら、[T]の形がwell-formedであることを調べる帰納的な[has_type]の呼び出しがないからです。
    同様に[T_Abs]の場合、[well_formed_ty T11] の証明を必要とします。
    なぜなら、[has_type]の帰納的呼び出しは [T12] がwell-formedであることだけを保証するからです。
 
    読者が記述しなければならない規則の中で[well_formed_ty]チェックが必要なのは、
    [tnil]の場合だけです。 *)

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      well_formed_ty T ->
      Gamma |- (tvar x) \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      well_formed_ty T11 ->
      (extend Gamma x T11) |- t12 \in T12 -> 
      Gamma |- (tabs x T11 t12) \in (TArrow T11 T12)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |- t1 \in (TArrow T1 T2) -> 
      Gamma |- t2 \in T1 -> 
      Gamma |- (tapp t1 t2) \in T2
  (* records: *)
  | T_Proj : forall Gamma i t Ti Tr,
      Gamma |- t \in Tr ->
      Tlookup i Tr = Some Ti ->
      Gamma |- (tproj t i) \in Ti
  | T_RNil : forall Gamma,
      Gamma |- trnil \in TRNil
  | T_RCons : forall Gamma i t T tr Tr,
      Gamma |- t \in T ->
      Gamma |- tr \in Tr ->
      record_ty Tr ->
      record_tm tr ->
      Gamma |- (trcons i t tr) \in (TRCons i T Tr)

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_Abs" | Case_aux c "T_App"
  | Case_aux c "T_Proj" | Case_aux c "T_RNil" | Case_aux c "T_RCons" ].

(* ###################################################################### *)
(*
(** ** Examples *)
*)
(** ** 例 *)

(*
(** **** Exercise: 2 stars (examples)  *)
*)
(** **** 練習問題: ★★ (examples)  *)
(*
(** Finish the proofs. *)
*)
(** 証明を完成させなさい。 *)

(*
(** Feel free to use Coq's automation features in this proof.
    However, if you are not confident about how the type system works,
    you may want to carry out the proof first using the basic
    features ([apply] instead of [eapply], in particular) and then
    perhaps compress it using automation. *)
*)
(** 証明の中ではCoq の自動化機能を自由に使って構いません。
    しかし、もし型システムがどのように動作するか確信できていないなら、
    最初に基本機能(特に[eapply]ではなく[apply])を使った証明を行い、
    次に自動化を使ってその証明を圧縮するのがよいかもしれません。 *)

Lemma typing_example_2 : 
  empty |- 
    (tapp (tabs a (TRCons i1 (TArrow A A)
                      (TRCons i2 (TArrow B B)
                       TRNil))
              (tproj (tvar a) i2))
            (trcons i1 (tabs a A (tvar a)) 
            (trcons i2 (tabs a B (tvar a))
             trnil))) \in
    (TArrow B B).
Proof. 
  (* FILL IN HERE *) Admitted.

(*
(** Before starting to prove this fact (or the one above!), make sure
    you understand what it is saying. *)
*)
(** 次の事実(あるいはすぐ上の事実も!)の証明を始める前に、
    それが何を主張しているかを確認しなさい。 *)

Example typing_nonexample : 
  ~ exists T,
      (extend empty a (TRCons i2 (TArrow A A) 
                                TRNil)) |-
               (trcons i1 (tabs a B (tvar a)) (tvar a)) \in
               T.
Proof.
  (* FILL IN HERE *) Admitted.

Example typing_nonexample_2 : forall y,
  ~ exists T,
    (extend empty y A) |-
           (tapp (tabs a (TRCons i1 A TRNil)
                     (tproj (tvar a) i1))
                   (trcons i1 (tvar y) (trcons i2 (tvar y) trnil))) \in
           T.
Proof.
  (* FILL IN HERE *) Admitted.

(* ###################################################################### *)
(*
(** ** Properties of Typing *)
*)
(** ** 型付けの性質 *)

(*
(** The proofs of progress and preservation for this system are
    essentially the same as for the pure simply typed lambda-calculus,
    but we need to add some technical lemmas involving records. *)
*)
(** このシステムの進行と保存の証明は、純粋な単純型付きラムダ計算のものと本質的に同じです。
    しかし、レコードについての技術的補題を追加する必要があります。 *)

(* ###################################################################### *)
(** *** Well-Formedness *)

Lemma wf_rcd_lookup : forall i T Ti,
  well_formed_ty T ->
  Tlookup i T = Some Ti ->
  well_formed_ty Ti.
Proof with eauto.
  intros i T.
  T_cases (induction T) Case; intros; try solve by inversion.
  Case "TRCons".
    inversion H. subst. unfold Tlookup in H0.
    destruct (eq_id_dec i i0)...
    inversion H0. subst...  Qed.

Lemma step_preserves_record_tm : forall tr tr',
  record_tm tr ->
  tr ==> tr' ->
  record_tm tr'.
Proof.
  intros tr tr' Hrt Hstp.
  inversion Hrt; subst; inversion Hstp; subst; auto.
Qed.

Lemma has_type__wf : forall Gamma t T,
  Gamma |- t \in T -> well_formed_ty T.
Proof with eauto.
  intros Gamma t T Htyp.
  has_type_cases (induction Htyp) Case...
  Case "T_App".
    inversion IHHtyp1... 
  Case "T_Proj".
    eapply wf_rcd_lookup...
Qed.

(* ###################################################################### *)
(*
(** *** Field Lookup *)
*)
(** *** フィールドのルックアップ *)

(*
(** Lemma: If [empty |- v : T] and [Tlookup i T] returns [Some Ti],
     then [tlookup i v] returns [Some ti] for some term [ti] such
     that [empty |- ti \in Ti].

    Proof: By induction on the typing derivation [Htyp].  Since
      [Tlookup i T = Some Ti], [T] must be a record type, this and
      the fact that [v] is a value eliminate most cases by inspection,
      leaving only the [T_RCons] case.

      If the last step in the typing derivation is by [T_RCons], then
      [t = trcons i0 t tr] and [T = TRCons i0 T Tr] for some [i0],
      [t], [tr], [T] and [Tr].

      This leaves two possiblities to consider - either [i0 = i] or
      not.

      - If [i = i0], then since [Tlookup i (TRCons i0 T Tr) = Some
        Ti] we have [T = Ti].  It follows that [t] itself satisfies
        the theorem.

      - On the other hand, suppose [i <> i0].  Then 
        Tlookup i T = Tlookup i Tr
        and 
        tlookup i t = tlookup i tr,
        so the result follows from the induction hypothesis. [] *)
*)
(** 補題: もし [empty |- v : T] で、かつ [ty_lookup i T] が [Some Ti] を返すならば,
     [tm_lookup i v] はある項 [ti] について [Some ti] を返す。
     ただし、[empty |- ti \in Ti] となる。
 
    証明: 型の導出[Htyp]についての帰納法で証明する。
      [ty_lookup i T = Some Ti] であることから、
      [T] はレコード型でなければならない。
      このことと[v]が値であることから、ほとんどの場合は精査で除去でき、
      [T_RCons]の場合だけが残る。
 
      型導出の最後のステップが[T_RCons]によるものであるとき、
      ある[i0]、[t]、[tr]、[T]、[Tr]について
      [t = trcons i0 t tr] かつ [T = TRCons i0 T Tr] である。
 
      このとき2つの可能性が残る。[i0 = i] か、そうでないかである。
 
      - [i = i0] のとき、[Tlookup i (TRCons i0 T Tr) = Some Ti] から
        [T = Ti] となる。これから [t]自身が定理を満たすことが言える。
 
      - 一方、[i <> i0] とする。すると
        Tlookup i T = Tlookup i Tr
        かつ
        tlookup i t = tlookup i tr
        となる。
        これから、帰納法の仮定より結果が得られる。*)

Lemma lookup_field_in_value : forall v T i Ti,
  value v ->
  empty |- v \in T ->
  Tlookup i T = Some Ti ->
  exists ti, tlookup i v = Some ti /\ empty |- ti \in Ti.
Proof with eauto.
  intros v T i Ti Hval Htyp Hget.
  remember (@empty ty) as Gamma.
  has_type_cases (induction Htyp) Case; subst; try solve by inversion...
  Case "T_RCons".
    simpl in Hget. simpl. destruct (eq_id_dec i i0).
    SCase "i is first".
      simpl. inversion Hget. subst.
      exists t...
    SCase "get tail".
      destruct IHHtyp2 as [vi [Hgeti Htypi]]...
      inversion Hval... Qed.

(* ###################################################################### *)
(*
(** *** Progress *)
*)
(** *** 進行 *)

Theorem progress : forall t T, 
     empty |- t \in T ->
     value t \/ exists t', t ==> t'. 
Proof with eauto.
  (* Theorem: Suppose empty |- t : T.  Then either
       1. t is a value, or
       2. t ==> t' for some t'.
     Proof: By induction on the given typing derivation. *)
  (* 定理: empty |- t : T と仮定する。すると
       1. t は値である、または
       2. ある t' について t ==> t'
     のいずれかが成立する。
     証明: 与えられた型の導出についての帰納法より。 *)
  intros t T Ht.
  remember (@empty ty) as Gamma.
  generalize dependent HeqGamma.
  has_type_cases (induction Ht) Case; intros HeqGamma; subst.
  Case "T_Var".
    (* The final rule in the given typing derivation cannot be [T_Var],
       since it can never be the case that [empty |- x : T] (since the
       context is empty). *)
    (* 型導出の最後の規則は[T_Var]ではあり得ない。なぜなら、
       (コンテキストが empty であることから) [empty |- x : T] になることはないからである。*)
    inversion H.
  Case "T_Abs".
    (* If the [T_Abs] rule was the last used, then [t = tabs x T11 t12],
       which is a value. *)
    (* もし[T_Abs]規則が最後に使われたものならば、[t = tabs x T11 t12] となる。
       これは値である。 *)
    left...
  Case "T_App".
    (* If the last rule applied was T_App, then [t = t1 t2], and we know 
       from the form of the rule that
         [empty |- t1 : T1 -> T2]
         [empty |- t2 : T1]
       By the induction hypothesis, each of t1 and t2 either is a value 
       or can take a step. *)
    (* もし最後に適用された規則が[T_App]ならば、[t = t1 t2] となる。
       規則の形から
         [empty |- t1 : T1 -> T2]
         [empty |- t2 : T1]
       となる。
       帰納法の仮定より、t1 と t2 のそれぞれは、値であるかステップを進むことができる。 *)
    right.
    destruct IHHt1; subst...
    SCase "t1 is a value".
      destruct IHHt2; subst...
      SSCase "t2 is a value".
      (* If both [t1] and [t2] are values, then we know that 
         [t1 = tabs x T11 t12], since abstractions are the only values
         that can have an arrow type.  But 
         [(tabs x T11 t12) t2 ==> [x:=t2]t12] by [ST_AppAbs]. *)
      (* もし[t1]と[t2]が共に値ならば、[t1 = tabs x T11 t12] となる。
         なぜなら関数型の値は関数抽象だけだからである。
         しかし[ST_AppAbs]より
         [(tabs x T11 t12) t2 ==> [x:=t2]t12] となる。 *)
        inversion H; subst; try (solve by inversion).
        exists ([x:=t2]t12)...
      SSCase "t2 steps".
        (* If [t1] is a value and [t2 ==> t2'], then [t1 t2 ==> t1 t2'] 
           by [ST_App2]. *)
        (* もし [t1] が値で [t2 ==> t2'] ならば、[ST_App2] より [t1 t2 ==> t1 t2']
           となる。 *)
        destruct H0 as [t2' Hstp]. exists (tapp t1 t2')...
    SCase "t1 steps".
      (* Finally, If [t1 ==> t1'], then [t1 t2 ==> t1' t2] by [ST_App1]. *)
      (* 最後に、もし [t1 ==> t1'] ならば[ST_App1]より [t1 t2 ==> t1' t2] である。 *)
      destruct H as [t1' Hstp]. exists (tapp t1' t2)...
  Case "T_Proj".
    (* If the last rule in the given derivation is [T_Proj], then 
       [t = tproj t i] and
           [empty |- t : (TRcd Tr)]
       By the IH, [t] either is a value or takes a step. *)
    (* もし与えられた導出の最後の規則が[T_Proj]ならば、
       [t = tproj t i] かつ
           [empty |- t : (TRcd Tr)] である。
       帰納仮定より、[t] は値であるかステップを進むことができる。 *)
    right. destruct IHHt...
    SCase "rcd is value".
      (* If [t] is a value, then we may use lemma
         [lookup_field_in_value] to show [tlookup i t = Some ti] for
         some [ti] which gives us [tproj i t ==> ti] by [ST_ProjRcd]
         *)
      (* もし [t] が値ならば、補題[lookup_field_in_value]を使うと、
         ある[ti]について[tlookup i t = Some ti]が言える。
         このとき[ST_ProjRcd]より [tproj i t ==> ti] となる。*)
      destruct (lookup_field_in_value _ _ _ _ H0 Ht H) as [ti [Hlkup _]].
      exists ti...
    SCase "rcd_steps".
      (* On the other hand, if [t ==> t'], then [tproj t i ==> tproj t' i]
         by [ST_Proj1]. *)
      (* 一方、もし [t ==> t'] ならば、[ST_Proj1]により [tproj t i ==> tproj t' i]
         となる。 *)
      destruct H0 as [t' Hstp]. exists (tproj t' i)...
  Case "T_RNil".
    (* If the last rule in the given derivation is [T_RNil], then 
       [t = trnil], which is a value. *)
    (* もし与えられた導出の最後の規則が[T_RNil]ならば、
       [t = trnil] となるが、これは値である。 *)
    left...
  Case "T_RCons".
    (* If the last rule is [T_RCons], then [t = trcons i t tr] and
         [empty |- t : T]
         [empty |- tr : Tr]
       By the IH, each of [t] and [tr] either is a value or can take
       a step. *)
    (* もし最後の規則が[T_RCons]ならば、[t = trcons i t tr] かつ
         [empty |- t : T]
         [empty |- tr : Tr]
       となる。帰納仮定から、[t]と[tr]はそれぞれ値であるか、ステップを進むことができる。 *)
    destruct IHHt1...
    SCase "head is a value".
      destruct IHHt2; try reflexivity.
      SSCase "tail is a value".
      (* If [t] and [tr] are both values, then [trcons i t tr]
         is a value as well. *)
      (* もし[t]と[tr]が両者とも値ならば、[trcons i t tr] も値である。*)
        left...
      SSCase "tail steps".
        (* If [t] is a value and [tr ==> tr'], then 
           [trcons i t tr ==> trcons i t tr'] by 
           [ST_Rcd_Tail]. *)
        (* もし [t] が値で [tr ==> tr'] ならば、[ST_Rcd_Tail]より
           [trcons i t tr ==> trcons i t tr'] となる。 *)
        right. destruct H2 as [tr' Hstp].
        exists (trcons i t tr')...
    SCase "head steps".      
      (* If [t ==> t'], then 
         [trcons i t tr ==> trcons i t' tr] 
         by [ST_Rcd_Head]. *)
      (* もし [t ==> t'] ならば、[ST_Rcd_Head]より
         [trcons i t tr ==> trcons i t' tr] となる。 *)
      right. destruct H1 as [t' Hstp].
      exists (trcons i t' tr)...  Qed.

(* ###################################################################### *)
(*
(** *** Context Invariance *)
*)
(** *** コンテキスト不変性 *)

Inductive appears_free_in : id -> tm -> Prop :=
  | afi_var : forall x,
      appears_free_in x (tvar x)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x (tapp t1 t2)
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x (tapp t1 t2)
  | afi_abs : forall x y T11 t12,
        y <> x  ->
        appears_free_in x t12 ->
        appears_free_in x (tabs y T11 t12)
  | afi_proj : forall x t i,
     appears_free_in x t ->
     appears_free_in x (tproj t i)
  | afi_rhead : forall x i ti tr,
      appears_free_in x ti ->
      appears_free_in x (trcons i ti tr)
  | afi_rtail : forall x i ti tr,
      appears_free_in x tr ->
      appears_free_in x (trcons i ti tr).

Hint Constructors appears_free_in.

Lemma context_invariance : forall Gamma Gamma' t S,
     Gamma |- t \in S  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x)  ->
     Gamma' |- t \in S.
Proof with eauto.
  intros. generalize dependent Gamma'.
  has_type_cases (induction H) Case; 
    intros Gamma' Heqv...
  Case "T_Var".
    apply T_Var... rewrite <- Heqv...
  Case "T_Abs".
    apply T_Abs... apply IHhas_type. intros y Hafi.
    unfold extend. destruct (eq_id_dec x y)...
  Case "T_App".
    apply T_App with T1...
  Case "T_RCons".
    apply T_RCons...  Qed.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   Gamma |- t \in T ->
   exists T', Gamma x = Some T'.
Proof with eauto.
  intros x t T Gamma Hafi Htyp.
  has_type_cases (induction Htyp) Case; inversion Hafi; subst...
  Case "T_Abs".
    destruct IHHtyp as [T' Hctx]... exists T'.
    unfold extend in Hctx. 
    rewrite neq_id in Hctx... 
Qed.

(* ###################################################################### *)
(*
(** *** Preservation *)
*)
(** *** 保存 *)

Lemma substitution_preserves_typing : forall Gamma x U v t S,
     (extend Gamma x U) |- t \in S  ->
     empty |- v \in U   ->
     Gamma |- ([x:=v]t) \in S.
Proof with eauto.
  (* Theorem: If Gamma,x:U |- t : S and empty |- v : U, then 
     Gamma |- ([x:=v]t) S. *)
  (* 定理: もし Gamma,x:U |- t : S かつ empty |- v : U ならば
     Gamma |- ([x:=v]t) S. である。 *)
  intros Gamma x U v t S Htypt Htypv. 
  generalize dependent Gamma. generalize dependent S.
  (* Proof: By induction on the term t.  Most cases follow directly
     from the IH, with the exception of tvar, tabs, trcons.
     The former aren't automatic because we must reason about how the
     variables interact. In the case of trcons, we must do a little
     extra work to show that substituting into a term doesn't change
     whether it is a record term. *)
  (* 証明: 項tについての帰納法で証明する。ほとんどの場合は帰納仮定から直接得られる。
     そうでないのは tvar、 tabs、trcons だけである。
     最初の2つの場合は、変数の相互作用について推論する必要があるため自動化できない。
     trconsの場合は、
     置換によってレコード項であるか否かが変化しないことを示すために多少余分な仕事が必要である。 *)
  t_cases (induction t) Case;
    intros S Gamma Htypt; simpl; inversion Htypt; subst...
  Case "tvar".
    simpl. rename i into y.
    (* If t = y, we know that
         [empty |- v : U] and
         [Gamma,x:U |- y : S]
       and, by inversion, [extend Gamma x U y = Some S].  We want to
       show that [Gamma |- [x:=v]y : S].

       There are two cases to consider: either [x=y] or [x<>y]. *)
    (* もし t = y ならば
         [empty |- v : U] かつ
         [Gamma,x:U |- y : S] となる。
       inversion より [extend Gamma x U y = Some S] が得られる。
       示したいことは [Gamma |- [x:=v]y : S] である。

       2つの場合に分けて考える: [x=y] の場合と [x<>y] の場合である。 *)
    destruct (eq_id_dec x y). 
    SCase "x=y".
    (* If [x = y], then we know that [U = S], and that [[x:=v]y = v].
       So what we really must show is that if [empty |- v : U] then
       [Gamma |- v : U].  We have already proven a more general version
       of this theorem, called context invariance. *)
    (* もし [x = y] ならば、[U = S] かつ [[x:=v]y = v] となる。
       これから、実際に示さなければならないのは、[empty |- v : U] ならば
       [Gamma |- v : U] ということである。
       これについては、より一般性のあるバージョンを既に証明している。
       それはコンテキスト不変性である。 *)
      subst.
      unfold extend in H0. rewrite eq_id in H0. 
      inversion H0; subst. clear H0.
      eapply context_invariance...
      intros x Hcontra.
      destruct (free_in_context _ _ S empty Hcontra) as [T' HT']...
      inversion HT'.
    SCase "x<>y".
    (* If [x <> y], then [Gamma y = Some S] and the substitution has no
       effect.  We can show that [Gamma |- y : S] by [T_Var]. *)
    (* もし [x <> y] ならば、[Gamma y = Some S] であり置換は何も影響しない。
       [T_Var]から[Gamma |- y : S]を示すことができる。 *)
      apply T_Var... unfold extend in H0. rewrite neq_id in H0... 
  Case "tabs".
    rename i into y. rename t into T11.
    (* If [t = tabs y T11 t0], then we know that
         [Gamma,x:U |- tabs y T11 t0 : T11->T12]
         [Gamma,x:U,y:T11 |- t0 : T12]
         [empty |- v : U]
       As our IH, we know that forall S Gamma, 
         [Gamma,x:U |- t0 : S -> Gamma |- [x:=v]t0 S].
    
       We can calculate that 
         [x:=v]t = tabs y T11 (if beq_id x y then t0 else [x:=v]t0)
       And we must show that [Gamma |- [x:=v]t : T11->T12].  We know
       we will do so using [T_Abs], so it remains to be shown that:
         [Gamma,y:T11 |- if beq_id x y then t0 else [x:=v]t0 : T12]
       We consider two cases: [x = y] and [x <> y].
    *)
    (* もし [t = tabs y T11 t0] ならば、
         [Gamma,x:U |- tabs y T11 t0 : T11->T12]
         [Gamma,x:U,y:T11 |- t0 : T12]
         [empty |- v : U]
       である。帰納仮定から、すべての S Gamma について
         [Gamma,x:U |- t0 : S -> Gamma |- [x:=v]t0 S] となる。

       次のように計算ができる:
         [x:=v]t = tabs y T11 (if beq_id x y then t0 else [x:=v]t0)
       示さなければならないのは [Gamma |- [x:=v]t : T11->T12] である。
       [T_Abs]を使うために、残っているのは次を示すことである:
         [Gamma,y:T11 |- if beq_id x y then t0 else [x:=v]t0 : T12]
       2つの場合に分けて考える: [x = y] の場合と [x <> y] の場合である。
    *)
    apply T_Abs...
    destruct (eq_id_dec x y).
    SCase "x=y".
    (* If [x = y], then the substitution has no effect.  Context
       invariance shows that [Gamma,y:U,y:T11] and [Gamma,y:T11] are
       equivalent.  Since the former context shows that [t0 : T12], so
       does the latter. *)
    (* [x = y] の場合、置換は影響しない。
       コンテキスト不変性により [Gamma,y:U,y:T11] と [Gamma,y:T11] 
       が同値であることが示される。
       前者のコンテキストから [t0 : T12] が言えるので、後者も同様になる。 *)
      eapply context_invariance...
      subst.
      intros x Hafi. unfold extend.
      destruct (eq_id_dec y x)...
    SCase "x<>y".
    (* If [x <> y], then the IH and context invariance allow us to show that
         [Gamma,x:U,y:T11 |- t0 : T12]       =>
         [Gamma,y:T11,x:U |- t0 : T12]       =>
         [Gamma,y:T11 |- [x:=v]t0 : T12] *)
    (* [x <> y] の場合、帰納仮定とコンテキスト不変性から
         [Gamma,x:U,y:T11 |- t0 : T12]       =>
         [Gamma,y:T11,x:U |- t0 : T12]       =>
         [Gamma,y:T11 |- [x:=v]t0 : T12] となる。 *)
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold extend.
      destruct (eq_id_dec y z)... 
      subst. rewrite neq_id...
  Case "trcons".
    apply T_RCons... inversion H7; subst; simpl...
Qed.

Theorem preservation : forall t t' T,
     empty |- t \in T  ->
     t ==> t'  ->
     empty |- t' \in T.
Proof with eauto.
  intros t t' T HT.
  (* Theorem: If [empty |- t : T] and [t ==> t'], then [empty |- t' : T]. *)
  (* 定理: [empty |- t : T] かつ [t ==> t'] ならば [empty |- t' : T] である。 *)
  remember (@empty ty) as Gamma. generalize dependent HeqGamma.
  generalize dependent t'.
  (* Proof: By induction on the given typing derivation.  Many cases are
     contradictory ([T_Var], [T_Abs]) or follow directly from the IH
     ([T_RCons]).  We show just the interesting ones. *)
  (* 証明: 型導出についての帰納法を使う。
     ほとんどの場合は矛盾が得られるか([T_Var]、[T_Abs])、帰納仮定から直接得られる([T_RCons])。
     興味深いものだけを示す。*)
  has_type_cases (induction HT) Case; 
    intros t' HeqGamma HE; subst; inversion HE; subst...
  Case "T_App".
    (* If the last rule used was [T_App], then [t = t1 t2], and three rules
       could have been used to show [t ==> t']: [ST_App1], [ST_App2], and 
       [ST_AppAbs]. In the first two cases, the result follows directly from 
       the IH. *)
    (* 最後に使われた規則が[T_App]の場合、[t = t1 t2] である。このとき [t ==> t']
       を示すのに使われた可能性がある規則は3つ:[ST_App1]、[ST_App2]、[ST_AppAbs] である。
       最初の2つについては、帰納仮定から直接結果が得られる。 *)
    inversion HE; subst...
    SCase "ST_AppAbs".
      (* For the third case, suppose 
           [t1 = tabs x T11 t12]
         and
           [t2 = v2].  We must show that [empty |- [x:=v2]t12 : T2]. 
         We know by assumption that
             [empty |- tabs x T11 t12 : T1->T2]
         and by inversion
             [x:T1 |- t12 : T2]
         We have already proven that substitution_preserves_typing and 
             [empty |- v2 : T1]
         by assumption, so we are done. *)
      (* 3つ目の規則の場合、次を仮定する:
           [t1 = tabs x T11 t12]
         かつ
           [t2 = v2]。 示すべきことは [empty |- [x:=v2]t12 : T2] である。
         仮定から
             [empty |- tabs x T11 t12 : T1->T2]
         であり、inversion から
             [x:T1 |- t12 : T2]
         である。substitution_preserves_typing を既に証明しており、
         仮定から [empty |- v2 : T1] であるから、証明は完了する。 *)
      apply substitution_preserves_typing with T1...
      inversion HT1...
  Case "T_Proj".
  (* If the last rule was [T_Proj], then [t = tproj t1 i].  Two rules
     could have caused [t ==> t']: [T_Proj1] and [T_ProjRcd].  The typing
     of [t'] follows from the IH in the former case, so we only
     consider [T_ProjRcd].

     Here we have that [t] is a record value.  Since rule T_Proj was
     used, we know [empty |- t \in Tr] and [Tlookup i Tr = Some
     Ti] for some [i] and [Tr].  We may therefore apply lemma
     [lookup_field_in_value] to find the record element this
     projection steps to. *)
  (* 最後の規則が[T_Proj]のとき、[t = tproj t1 i] である。
     [t ==> t'] のために2つの規則が使われた可能性がある。
     [T_Proj1] または [T_ProjRcd] である。前者の場合、帰納仮定から[t']の型付けが得られる。
     そのため、[T_ProjRcd]の場合だけを考える。

     ここで[t]はレコード値である。規則 T_Proj が使われたことから、ある[i]と[Tr]
     について、[empty |- t \in Tr] かつ [Tlookup i Tr = Some Ti] となる。
     したがって、この射影がステップするレコード要素を見つけるため、
     補題[lookup_field_in_value]を適用することができる。 *)
    destruct (lookup_field_in_value _ _ _ _ H2 HT H)
      as [vi [Hget Htyp]].
    rewrite H4 in Hget. inversion Hget. subst...
  Case "T_RCons".
  (* If the last rule was [T_RCons], then [t = trcons i t tr] for
     some [i], [t] and [tr] such that [record_tm tr].  If the step is
     by [ST_Rcd_Head], the result is immediate by the IH.  If the step
     is by [ST_Rcd_Tail], [tr ==> tr2'] for some [tr2'] and we must also
     use lemma [step_preserves_record_tm] to show [record_tm tr2']. *)
  (* 最後の規則が[T_RCons]の場合、ある[i]、[t]、[tr]について [t = trcons i t tr] 
     で、また[record_tm tr]である。ステップが[ST_Rcd_Head]によるものである場合、
     帰納仮定から直接結果が得られる。ステップが[ST_Rcd_Tail]によるものである場合、
     ある[tr2']について [tr ==> tr2'] である。[record_tm tr2']
     を示すためには同様に補題[step_preserves_record_tm]を使う。*)
    apply T_RCons... eapply step_preserves_record_tm...
Qed.
(** [] *)

End STLCExtendedRecords.

(** $Date: 2014-12-31 11:17:56 -0500 (Wed, 31 Dec 2014) $ *)

