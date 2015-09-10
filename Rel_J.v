(* * Rel: Properties of Relations *)
(** * Rel_J:関係の性質 *)

Require Export SfLib_J.

(* This short, optional chapter develops some basic definitions and a
    few theorems about binary relations in Coq.  The key definitions
    are repeated where they are actually used (in the [Smallstep]
    chapter), so readers who are already comfortable with these ideas
    can safely skim or skip this chapter.  However, relations are also
    a good source of exercises for developing facility with Coq's
    basic reasoning facilities, so it may be useful to look at it just
    after the [Logic] chapter. *)
(** この短い章では、いくつかの基本的な定義と二項関係の定理の証明を行います。重要な定義は後に
    [Smallstep_J]章におけるスモールステップ操作的意味論で再度定義されます。
    もしこれらに慣れているならばこの章を飛ばしても問題ありません。
    しかし、Coqの基本的推論機構を使う良い練習問題ともなるので、
    [Logic_J]章の直後で見ておくのがよいかもしれません。 *)

(* A (binary) _relation_ on a set [X] is a family of propositions
    parameterized by two elements of [X] -- i.e., a proposition about
    pairs of elements of [X].  *)
(** 集合[X]の「上の」（二項）関係は、[X]2つをパラメータとする命題です。-- 
    つまり、集合[X]の2つの要素に関する論理的主張です。*)

Definition relation (X: Type) := X->X->Prop.

(* Somewhat confusingly, the Coq standard library hijacks the generic
    term "relation" for this specific instance. To maintain
    consistency with the library, we will do the same.  So, henceforth
    the Coq identifier [relation] will always refer to a binary
    relation between some set and itself, while the English word
    "relation" can refer either to the specific Coq concept or the
    more general concept of a relation between any number of possibly
    different sets.  The context of the discussion should always make
    clear which is meant. *)
(** 若干まぎらわしいことに、Coqの標準ライブラリでは、一般的な用語"関係(relation)"を、
    この特定の場合(つまり1つの集合上の二項関係)を指すためだけに使っています。
    ライブラリとの整合性を保つために、ここでもそれに従います。
    したがって、Coq の識別子[relation]は常に、集合上の二項関係を指すために使います。
    一方、日本語の"関係"は、Coq の relation を指す場合もあれば、
    より一般の任意の数の(それぞれ別のものかもしれない)集合の間の関係を指す場合もあります。
    どちらを指しているかは常に議論の文脈から明らかになるようにします。 *)

(** An example relation on [nat] is [le], the less-that-or-equal-to
    relation which we usually write like this [n1 <= n2]. *)

Print le.
(* ====> Inductive le (n : nat) : nat -> Prop :=
             le_n : n <= n
           | le_S : forall m : nat, n <= m -> n <= S m *)
Check le : nat -> nat -> Prop.
Check le : relation nat.

(* ######################################################### *)
(* * Basic Properties of Relations *)
(** * 関係の基本性質 *)

(* As anyone knows who has taken an undergraduate discrete math
    course, there is a lot to be said about relations in general --
    ways of classifying relations (are they reflexive, transitive,
    etc.), theorems that can be proved generically about classes of
    relations, constructions that build one relation from another,
    etc.  For example... *)
(** 大学の離散数学の講義で習っているように、関係を「一般的に」議論し記述する方法がいくつもあります。
    -- 関係を分類する方法(反射的か、推移的か、など)、関係のクラスについて一般的に証明できる定理、
    関係からの別の関係の構成、などです。例えば... *)

(* A relation [R] on a set [X] is a _partial function_ if, for every
    [x], there is at most one [y] such that [R x y] -- i.e., if [R x
    y1] and [R x y2] together imply [y1 = y2]. *)
(** 集合[X]上の関係[R]は、次の条件を満たすとき、部分関数(_partial function_)です。
    条件とは、すべての[x]に対して、[R x y]となる[y]は高々1つであるということ
    -- つまり、[R x y1]かつ[R x y2]ならば [y1 = y2] となることです。*)

Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2. 

(* For example, the [next_nat] relation defined earlier is a partial
    function. *)
(** 例えば、[Logic_J]で定義した[next_nat]関係は部分関数です。*)

Print next_nat.
(* ====> Inductive next_nat (n : nat) : nat -> Prop := 
           nn : next_nat n (S n) *)
Check next_nat : relation nat.

Theorem next_nat_partial_function : 
   partial_function next_nat.
Proof. 
  unfold partial_function.
  intros x y1 y2 H1 H2.
  inversion H1. inversion H2.
  reflexivity.  Qed. 

(* However, the [<=] relation on numbers is not a partial function.
    In short: Assume, for a contradiction, that [<=] is a partial
    function.  But then, since [0 <= 0] and [0 <= 1], it follows that
    [0 = 1].  This is nonsense, so our assumption was
    contradictory. *)
(** しかし、数値上の[<=]関係は部分関数ではありません。
    これは矛盾を導くことで示すことができます。簡単にいうと: [<=]が部分関数であると仮定します。
    すると、[0<=0]かつ[0<=1]から、[0=1]となります。これはおかしなことです。したがって、
    [<=]が部分関数だという仮定は矛盾するということになります。 *)

Theorem le_not_a_partial_function :
  ~ (partial_function le).
Proof.
  unfold not. unfold partial_function. intros Hc.
  assert (0 = 1) as Nonsense.
   Case "Proof of assertion".
   apply Hc with (x := 0). 
     apply le_n. 
     apply le_S. apply le_n. 
  inversion Nonsense.   Qed.

(* **** Exercise: 2 stars, optional  *)
(** **** 練習問題:★★, optional  *)
(* Show that the [total_relation] defined in earlier is not a partial
    function. *)
(** [Logic_J.v] に定義された [total_relation] が部分関数ではないことを示しなさい。 *)

(* FILL IN HERE *)
(** [] *)

(* **** Exercise: 2 stars, optional  *)
(** **** 練習問題:★★, optional  *)
(* Show that the [empty_relation] defined earlier is a partial
    function. *)
(** [Logic_J.v] に定義された [empty_relation] が部分関数であることを示しなさい。 *)

(* FILL IN HERE *)
(** [] *)

(* A _reflexive_ relation on a set [X] is one for which every element
    of [X] is related to itself. *)
(** 集合[X]上の反射的(_reflexive_)関係とは、[X]のすべての要素について、自身との関係が成立する関係です。 *)

Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.

Theorem le_reflexive :
  reflexive le.
Proof. 
  unfold reflexive. intros n. apply le_n.  Qed.

(* A relation [R] is _transitive_ if [R a c] holds whenever [R a b]
    and [R b c] do. *)
(** 関係[R]が推移的(_transitive_)であるとは、[R a b]かつ[R b c]ならば常に[R a c]
    となることです。 *)

Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).

Theorem le_trans :
  transitive le.
Proof.
  intros n m o Hnm Hmo.
  induction Hmo.
  Case "le_n". apply Hnm.
  Case "le_S". apply le_S. apply IHHmo.  Qed.

Theorem lt_trans:
  transitive lt.
Proof. 
  unfold lt. unfold transitive. 
  intros n m o Hnm Hmo.
  apply le_S in Hnm. 
  apply le_trans with (a := (S n)) (b := (S m)) (c := o).
  apply Hnm.
  apply Hmo. Qed.

(* **** Exercise: 2 stars, optional  *)
(** **** 練習問題:★★, optional  *)
(* We can also prove [lt_trans] more laboriously by induction,
    without using le_trans.  Do this.*)
(** [lt_trans] は、帰納法を使って手間をかければ、le_trans を使わずに証明することができます。
    これをやってみなさい。*)

Theorem lt_trans' :
  transitive lt.
Proof.
  (* Prove this by induction on evidence that [m] is less than [o]. *)
  (* [m]が[o]より小さい、という根拠についての帰納法で証明する *)
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [| m' Hm'o].
    (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 2 stars, optional  *)
(** **** 練習問題:★★, optional  *)
(* Prove the same thing again by induction on [o]. *)
(** 同じことを、[o]についての帰納法で証明しなさい。*)

Theorem lt_trans'' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction o as [| o'].
  (* FILL IN HERE *) Admitted.
(** [] *)

(* The transitivity of [le], in turn, can be used to prove some facts
    that will be useful later (e.g., for the proof of antisymmetry
    below)... *)
(** [le]の推移性は、同様に、後に(つまり以下の反対称性の証明において)
    有用な事実を証明するのに使うことができます... *)

Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof. 
  intros n m H. apply le_trans with (S n).
    apply le_S. apply le_n.
    apply H.  Qed.

(* **** Exercise: 1 star, optional  *)
(** **** 練習問題:★, optional *)
Theorem le_S_n : forall n m,
  (S n <= S m) -> (n <= m).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 2 stars, optional (le_Sn_n_inf)  *)
(** **** 練習問題:★★, optional (le_Sn_n_inf)  *)
(* Provide an informal proof of the following theorem:
 
    Theorem: For every [n], [~(S n <= n)]
 
    A formal proof of this is an optional exercise below, but try
    the informal proof without doing the formal proof first.
 
    Proof:
    (* FILL IN HERE *)
    []
  *)
(** 以下の定理の非形式的な証明を示しなさい。

    定理: すべての[n]について、[~(S n <= n)]

    形式的な証明はこの次のoptionalな練習問題ですが、
    ここでは、形式的な証明を行わずに、まず非形式的な証明を示しなさい。 

    証明:
    (* FILL IN HERE *)
    []
  *)

(* **** Exercise: 1 star, optional  *)
(** **** 練習問題:★, optional 　*)
Theorem le_Sn_n : forall n,
  ~ (S n <= n).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* Reflexivity and transitivity are the main concepts we'll need for
    later chapters, but, for a bit of additional practice working with
    relations in Coq, here are a few more common ones.

   A relation [R] is _symmetric_ if [R a b] implies [R b a]. *)
(** 反射性と推移性は後の章で必要となる主要概念ですが、Coq で関係を扱う練習をもう少ししましょう。
    次のいくつかの概念もよく知られたものです。

    関係[R]が対称的(_symmetric_)であるとは、[R a b]ならば[R b a]となることです。 *)

Definition symmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).

(* **** Exercise: 2 stars, optional  *)
(** **** 練習問題:★★, optional  *)
Theorem le_not_symmetric :
  ~ (symmetric le).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* A relation [R] is _antisymmetric_ if [R a b] and [R b a] together
    imply [a = b] -- that is, if the only "cycles" in [R] are trivial
    ones. *)
(** 関係[R]が反対称的(_antisymmetric_)であるとは、[R a b]かつ[R b a]ならば
    [a = b] となることです。 -- つまり、[R]における「閉路」は自明なものしかないということです。
    *)

Definition antisymmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

(* **** Exercise: 2 stars, optional  *)
(** **** 練習問題:★★, optional  *)
Theorem le_antisymmetric :
  antisymmetric le.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 2 stars, optional  *)
(** **** 練習問題:★★, optional  *)
Theorem le_step : forall n m p,
  n < m ->
  m <= S p ->
  n <= p.
Proof. 
  (* FILL IN HERE *) Admitted.
(** [] *)

(* A relation is an _equivalence_ if it's reflexive, symmetric, and
    transitive.  *)
(** 関係が同値関係(_equivalence_)であるとは、その関係が、
    反射的、対称的、かつ推移的であることです。 *)

Definition equivalence {X:Type} (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

(* A relation is a _partial order_ when it's reflexive,
    _anti_-symmetric, and transitive.  In the Coq standard library
    it's called just "order" for short. *)
(** 関係が半順序(_partial order_)であるとは、その関係が、
    反射的、反対称的、かつ推移的であることです。
    Coq 標準ライブラリでは、半順序のことを単に"順序(order)"と呼びます。*)

Definition order {X:Type} (R: relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).

(* A preorder is almost like a partial order, but doesn't have to be
    antisymmetric. *)
(** 前順序(preorder)とは、半順序の条件から反対称性を除いたものです。*)

Definition preorder {X:Type} (R: relation X) :=
  (reflexive R) /\ (transitive R).

Theorem le_order :
  order le.
Proof.
  unfold order. split. 
    Case "refl". apply le_reflexive.
    split. 
      Case "antisym". apply le_antisymmetric. 
      Case "transitive.". apply le_trans.  Qed.

(* ########################################################### *)
(* * Reflexive, Transitive Closure *)
(** * 反射推移閉包 *)

(* The _reflexive, transitive closure_ of a relation [R] is the
    smallest relation that contains [R] and that is both reflexive and
    transitive.  Formally, it is defined like this in the Relations
    module of the Coq standard library: *)
(** 関係[R]の反射推移閉包とは、[R]を含み反射性と推移性の両者を満たす最小の関係のことです。
    形式的には、Coq標準ライブラリのRelationモジュールで、以下のように定義されます。*)

Inductive clos_refl_trans {A: Type} (R: relation A) : relation A :=
    | rt_step : forall x y, R x y -> clos_refl_trans R x y
    | rt_refl : forall x, clos_refl_trans R x x
    | rt_trans : forall x y z,
          clos_refl_trans R x y ->
          clos_refl_trans R y z ->
          clos_refl_trans R x z.

(* For example, the reflexive and transitive closure of the
    [next_nat] relation coincides with the [le] relation. *)
(** 例えば、[next_nat]関係の反射推移閉包は[le]関係と同値になります。*)

Theorem next_nat_closure_is_le : forall n m,
  (n <= m) <-> ((clos_refl_trans next_nat) n m).
Proof.
  intros n m. split.
    Case "->".
      intro H. induction H.
      SCase "le_n". apply rt_refl.
      SCase "le_S".
        apply rt_trans with m. apply IHle. apply rt_step. apply nn.
    Case "<-".
      intro H. induction H.
      SCase "rt_step". inversion H. apply le_S. apply le_n.
      SCase "rt_refl". apply le_n.
      SCase "rt_trans".
        apply le_trans with y.
        apply IHclos_refl_trans1.
        apply IHclos_refl_trans2. Qed.

(* The above definition of reflexive, transitive closure is
    natural -- it says, explicitly, that the reflexive and transitive
    closure of [R] is the least relation that includes [R] and that is
    closed under rules of reflexivity and transitivity.  But it turns
    out that this definition is not very convenient for doing
    proofs -- the "nondeterminism" of the [rt_trans] rule can sometimes
    lead to tricky inductions.
 
    Here is a more useful definition... *)
(** 上の反射推移閉包の定義は自然です。--定義は[R]の反射推移閉包が
    [R]を含み反射律と推移律について閉じている最小の関係であることを明示的に述べています。
    しかし、この定義は、証明をする際にはあまり便利ではないのです。
    -- [rt_trans] 規則の"非決定性"によって、しばしばわかりにくい帰納法になってしまいます。

    以下は、より使いやすい定義です... *)

Inductive refl_step_closure {X:Type} (R: relation X) : relation X :=
  | rsc_refl  : forall (x : X), refl_step_closure R x x
  | rsc_step : forall (x y z : X),
                    R x y ->
                    refl_step_closure R y z ->
                    refl_step_closure R x z.

(* (Note that, aside from the naming of the constructors, this
    definition is the same as the [multi] step relation used in many
    other chapters.) *)
(** (なお、コンストラクタの命名を除けば、この定義は他の章で何度も使われる
    [multi] ステップ関係と同じものです。) *)

(* (The following [Tactic Notation] definitions are explained in
    another chapter.  You can ignore them if you haven't read the
    explanation yet.) *)
(** (以下の[Tactic Notation]の定義は Imp_J.v で説明されます。
    その章をまだ読んでいないならば、ここではそれを無視して構いません。) *)

Tactic Notation "rt_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "rt_step" | Case_aux c "rt_refl" 
  | Case_aux c "rt_trans" ].

Tactic Notation "rsc_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "rsc_refl" | Case_aux c "rsc_step" ].

(* Our new definition of reflexive, transitive closure "bundles"
    the [rt_step] and [rt_trans] rules into the single rule step.
    The left-hand premise of this step is a single use of [R],
    leading to a much simpler induction principle.
 
    Before we go on, we should check that the two definitions do
    indeed define the same relation...
    
    First, we prove two lemmas showing that [refl_step_closure] mimics
    the behavior of the two "missing" [clos_refl_trans]
    constructors.  *)
(** 新しい反射推移閉包の定義は、[rt_step]規則と[rt_trans]規則を「まとめ」て、
    1ステップの規則にします。
    このステップの左側は[R]を1回だけ使います。このことが帰納法をはるかに簡単なものにします。

    次に進む前に、二つの定義が同じものを定義していることを確認しなければなりません...

    最初に、[refl_step_closure]が、
    「失われた」2つの[clos_refl_trans]コンストラクタの働きを代替することを示す二つの補題を証明します。*)

Theorem rsc_R : forall (X:Type) (R:relation X) (x y : X),
       R x y -> refl_step_closure R x y.
Proof.
  intros X R x y H.
  apply rsc_step with y. apply H. apply rsc_refl.   Qed.

(* **** Exercise: 2 stars, optional (rsc_trans)  *)
(** **** 練習問題:★★, optional(rsc_trans)  *)
Theorem rsc_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      refl_step_closure R x y  ->
      refl_step_closure R y z ->
      refl_step_closure R x z.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* Then we use these facts to prove that the two definitions of
    reflexive, transitive closure do indeed define the same
    relation. *)
(** そして、反射推移閉包の2つの定義が同じ関係を定義していることを証明するために、
    上記の事実を使います。*)

(* **** Exercise: 3 stars, optional (rtc_rsc_coincide)  *)
(** **** 練習問題:★★★, optional (rtc_rsc_coincide)  *)
Theorem rtc_rsc_coincide : 
         forall (X:Type) (R: relation X) (x y : X),
  clos_refl_trans R x y <-> refl_step_closure R x y.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** $Date: 2014-12-31 15:31:47 -0500 (Wed, 31 Dec 2014) $ *)
