(** * Stlc: 単純型付きラムダ計算 *)
(*
(** * Stlc: The Simply Typed Lambda-Calculus *)
*)

(** The simply typed lambda-calculus (STLC) is a tiny core
    calculus embodying the key concept of _functional abstraction_,
    which shows up in pretty much every real-world programming
    language in some form (functions, procedures, methods, etc.).

    We will follow exactly the same pattern as in the previous chapter
    when formalizing this calculus (syntax, small-step semantics,
    typing rules) and its main properties (progress and preservation).
    The new technical challenges arise from the mechanisms of
    _variable binding_ and _substitution_.  It which will take some
    work to deal with these. *)
*)
(** 単純型付きラムダ計算(Simply Typed Lambda-Calculus, STLC)は、
    関数抽象(_functional abstraction_)を具現する、小さな、核となる計算体系です。
    関数抽象は、ほとんどすべての実世界のプログラミング言語に何らかの形
    (関数、手続き、メソッド等)で現れます。
 
    ここでは、この計算体系(構文、スモールステップ意味論、
    型付け規則)と主な性質(進行と保存)の形式化を、
    前の章でやったのとまったく同じパターンで行います。
    新しい技術的挑戦は、すべて変数束縛(_variable binding_)と置換(_substitution_)の機構から生じます。
    これらを扱うには少し作業がいります。 *)

Set Warnings "-notation-overridden,-parsing".
From PLF Require Import Maps.
From PLF Require Import Smallstep.
From PLF Require Import Types.

(* ################################################################# *)
(*
(** * Overview *)
*)
(** ** 概観 *)

(*
(** The STLC is built on some collection of _base types_: 
    booleans, numbers, strings, etc.  The exact choice of base types
    doesn't matter much -- the construction of the language and its
    theoretical properties work out the same no matter what we
    choose -- so for the sake of brevity let's take just [Bool] for
    the moment.  At the end of the chapter we'll see how to add more
    base types, and in later chapters we'll enrich the pure STLC with
    other useful constructs like pairs, records, subtyping, and
    mutable state.

    Starting from boolean constants and conditionals, we add three
    things:
        - variables
        - function abstractions
        - application

    This gives us the following collection of abstract syntax
    constructors (written out first in informal BNF notation -- we'll
    formalize it below). *)
*)
(** STLC は基本型(_base types_)の何らかの集まりの上に構成されます。
    基本型はブール型、数値、文字列などです。
    実際にどの基本型を入れるかは問題ではありません。
    どう選択しても、言語の構成とその理論的性質はまったく同じように導かれます。
    これから、簡潔にするため、しばらくは[Bool]だけとしましょう。
    この章の終わりには、さらに基本型を追加する方法がわかるでしょう。
    また後の章では、純粋なSTLCに、対、レコード、サブタイプ、
    変更可能状態などの他の便利な構成要素をとり入れてよりリッチなものにします。
 
    ブール値と条件分岐から始めて、3つのものを追加します:
        - 変数
        - 関数抽象
        - (関数)適用
 
    これから、以下の抽象構文コンストラクタが出てきます。
    （まずは非形式的BNF記法で書き出します。後に形式化します。） *)
(*
(**

       t ::= x                       variable
           | \x:T1.t2                abstraction
           | t1 t2                   application
           | true                    constant true
           | false                   constant false
           | if t1 then t2 else t3   conditional
*)
 *)
(** 
[[
       t ::= x                       変数
           | \x:T1.t2                関数抽象
           | t1 t2                   関数適用
           | true                    定数 true
           | false                   定数 false
           | if t1 then t2 else t3   条件式
]]
 *)

(*
(** The [\] symbol in a function abstraction [\x:T1.t2] is generally
    written as a Greek letter "lambda" (hence the name of the
    calculus).  The variable [x] is called the _parameter_ to the
    function; the term [t2] is its _body_.  The annotation [:T1]
    specifies the type of arguments that the function can be applied
    to. *)
*)
(** 関数抽象 [\x:T1.t2] の [\]記号はよくギリシャ文字のラムダ(λ)で記述されます（これがラムダ計算の名前の由来です）（訳注：日本語環境では円マークに見えることがあります）。
    変数[x]は関数のパラメータ(_parameter_)、項[t2]は関数の本体(_body_)と呼ばれます。
    付記された [:T] は関数が適用される引数の型を定めます。 *)

(*
(** Some examples:

      - [\x:Bool. x]

        The identity function for booleans.

      - [(\x:Bool. x) true]

        The identity function for booleans, applied to the boolean [true].

      - [\x:Bool. if x then false else true]

        The boolean "not" function.

      - [\x:Bool. true]

        The constant function that takes every (boolean) argument to
        [true]. *)
*)
(** 例をいくつか:
 
      - [\x:Bool. x] 
 
        ブール値の恒等関数。
 
      - [(\x:Bool. x) true] 
 
        ブール値[true]に適用された、ブール値の恒等関数。
 
      - [\x:Bool. if x then false else true] 
 
        ブール値の否定(not)関数。
 
      - [\x:Bool. true] 
 
        すべての(ブール値の)引数に対して[true]を返す定数関数。 *)
(*
(**
      - [\x:Bool. \y:Bool. x]

        A two-argument function that takes two booleans and returns
        the first one.  (As in Coq, a two-argument function is really
        a one-argument function whose body is also a one-argument
        function.)

      - [(\x:Bool. \y:Bool. x) false true]

        A two-argument function that takes two booleans and returns
        the first one, applied to the booleans [false] and [true].

        As in Coq, application associates to the left -- i.e., this
        expression is parsed as [((\x:Bool. \y:Bool. x) false) true].

      - [\f:Bool->Bool. f (f true)]

        A higher-order function that takes a _function_ [f] (from
        booleans to booleans) as an argument, applies [f] to [true],
        and applies [f] again to the result.

      - [(\f:Bool->Bool. f (f true)) (\x:Bool. false)]

        The same higher-order function, applied to the constantly
        [false] function. *)
*)
(** 
      - [\x:Bool. \y:Bool. x] 
 
        2つのブール値をとり、最初のものを返す2引数関数。
        （Coqと同様、2引数関数は、実際には本体が1引数関数である1引数関数です。）
 
      - [(\x:Bool. \y:Bool. x) false true] 
 
        2つのブール値をとり、最初のものを返す2引数関数を、ブール値[false]と[true]
        に適用したもの。
 
        Coqと同様、関数適用は左結合です。つまり、この式は
        [((\x:Bool. \y:Bool. x) false) true] と構文解析されます。
 
      - [\f:Bool->Bool. f (f true)] 
 
        （ブール値からブール値への）「関数」[f]を引数にとる高階関数。
        この高階関数は、[f]を[true]に適用し、その結果にさらに[f]を適用します。
 
      - [(\f:Bool->Bool. f (f true)) (\x:Bool. false)] 
 
        上記高階関数を、常に[false]を返す定数関数に適用したもの。 *)

(*
(** As the last several examples show, the STLC is a language of
    _higher-order_ functions: we can write down functions that take
    other functions as arguments and/or return other functions as
    results.

    The STLC doesn't provide any primitive syntax for defining _named_
    functions -- all functions are "anonymous."  We'll see in chapter
    [MoreStlc] that it is easy to add named functions to what we've
    got -- indeed, the fundamental naming and binding mechanisms are
    exactly the same.

    The _types_ of the STLC include [Bool], which classifies the
    boolean constants [true] and [false] as well as more complex
    computations that yield booleans, plus _arrow types_ that classify
    functions. *)
*)
(** 最後のいくつかの例で示されたように、STLCは高階(_higher-order_)関数の言語です。
    他の関数を引数として取る関数や、結果として他の関数を返す関数を書き下すことができます。
 
    STLCは、名前を持つ(_named_)関数を定義する基本構文を何も持っていません。
    すべての関数は「無名」("anonymous")です。
    後の[MoreStlc]章で、簡単にこの体系に名前を持つ関数を追加できることを見ます。
    実のところ、基本的な命名と束縛の機構はまったく同じです。
 
    STLCの型には[Bool]が含まれます。
    この型はブール定数[true]と[false]、および結果がブール値になるより複雑な計算の型です。
    その他に、関数の型である「関数型」(_arrow types_)があります。 *)
(*
(**

      T ::= Bool
          | T1 -> T2

    For example:

      - [\x:Bool. false] has type [Bool->Bool]

      - [\x:Bool. x] has type [Bool->Bool]

      - [(\x:Bool. x) true] has type [Bool]

      - [\x:Bool. \y:Bool. x] has type [Bool->Bool->Bool] 
                              (i.e., [Bool -> (Bool->Bool)])

      - [(\x:Bool. \y:Bool. x) false] has type [Bool->Bool]

      - [(\x:Bool. \y:Bool. x) false true] has type [Bool] *)
*)
(**
[[
      T ::= Bool 
          | T1 -> T2 
]]
    例えば:
 
      - [\x:Bool. false] は型 [Bool->Bool] を持ちます。
 
      - [\x:Bool. x] は型 [Bool->Bool] を持ちます。
 
      - [(\x:Bool. x) true] は型 [Bool] を持ちます。
 
      - [\x:Bool. \y:Bool. x] は型 [Bool->Bool->Bool] 
        （つまり [Bool -> (Bool->Bool)]）を持ちます。
 
      - [(\x:Bool. \y:Bool. x) false] は型 [Bool->Bool] を持ちます。
 
      - [(\x:Bool. \y:Bool. x) false true] は型 [Bool] を持ちます。 *)


(* ################################################################# *)
(*
(** * Syntax *)
*)
(** * 構文 *)

(** We next formalize the syntax of the STLC. *)

Module STLC.

(* ================================================================= *)
(*
(** ** Types *)
*)
(** ** 型 *)

Inductive ty : Type :=
  | TBool  : ty
  | TArrow : ty -> ty -> ty.

(* ================================================================= *)
(*
(** ** Terms *)
*)
(** ** 項 *)

Inductive tm : Type :=
  | tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : id -> ty -> tm -> tm
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm.

(*
(** Note that an abstraction [\x:T.t] (formally, [tabs x T t]) is
    always annotated with the type [T] of its parameter, in contrast
    to Coq (and other functional languages like ML, Haskell, etc.),
    which use type inference to fill in missing annotations.  We're
    not considering type inference here. *)
*)
(** この中では、関数抽象 [\x:T.t] （形式的には [tabs x T t]）には常にパラメータの型[T]が付記されます。
    これは Coq（あるいは他のML、Haskellといった関数型言語）のように、型推論(type inference)によって補うものと対照的です。
    ここでは型推論は考えません。 *)

(*
(** Some examples... *)
*)
(** いくつかの例... *)

Definition x := (Id "x").
Definition y := (Id "y").
Definition z := (Id "z").

Hint Unfold x.
Hint Unfold y.
Hint Unfold z.

(** [idB = \x:Bool. x] *)

Notation idB :=
  (tabs x TBool (tvar x)).

(** [idBB = \x:Bool->Bool. x] *)

Notation idBB :=
  (tabs x (TArrow TBool TBool) (tvar x)).

(** [idBBBB = \x:(Bool->Bool) -> (Bool->Bool). x] *)

Notation idBBBB :=
  (tabs x (TArrow (TArrow TBool TBool)
                      (TArrow TBool TBool))
    (tvar x)).

(** [k = \x:Bool. \y:Bool. x] *)

Notation k := (tabs x TBool (tabs y TBool (tvar x))).

(** [notB = \x:Bool. if x then false else true] *)

Notation notB := (tabs x TBool (tif (tvar x) tfalse ttrue)).

(*
(** (We write these as [Notation]s rather than [Definition]s to make
    things easier for [auto].) *)
*)
(** (これらを[Definition]ではなく[Notation]とすることで、[auto]に扱いやすくしています。) *)

(* ################################################################# *)
(*
(** * Operational Semantics *)
*)
(** * 操作的意味論 *)

(*
(** To define the small-step semantics of STLC terms, we begin,
    as always, by defining the set of values.  Next, we define the
    critical notions of _free variables_ and _substitution_, which are
    used in the reduction rule for application expressions.  And
    finally we give the small-step relation itself. *)
*)
(** STLC項のスモールステップ意味論を定義するために、いつものように、値の集合を定義することから始めます。
    次に、自由変数(_free variables_)と置換(_substitution_)という、重大な概念を定義します。
    これらは関数適用式の簡約規則に使われます。
    そして最後に、スモールステップ関係自体を与えます。 *)

(* ================================================================= *)
(*
(** ** Values *)
*)
(** ** 値 *)

(*
(** To define the values of the STLC, we have a few cases to consider.

    First, for the boolean part of the language, the situation is
    clear: [true] and [false] are the only values.  An [if]
    expression is never a value. *)
*)
(** STLCの値を定義するために、いくつかの場合を考えなければなりません。
 
    最初に、言語のブール値については、状況は明確です:
    [true]と[false]だけが値です。[if]式は決して値ではありません。 *)

(*
(** Second, an application is clearly not a value: It represents a
    function being invoked on some argument, which clearly still has
    work left to do. *)
*)
(** 二番目に、関数適用は明らかに値ではありません。
    関数適用は関数が何らかの引数に対して呼ばれたことを表しているのですから、
    明らかにこれからやることが残っています。 *)

(*
(** Third, for abstractions, we have a choice:

      - We can say that [\x:T. t1] is a value only when [t1] is a
        value -- i.e., only if the function's body has been
        reduced (as much as it can be without knowing what argument it
        is going to be applied to).

      - Or we can say that [\x:T. t1] is always a value, no matter
        whether [t1] is one or not -- in other words, we can say that
        reduction stops at abstractions.

    Our usual way of evaluating expressions in Coq makes the first
    choice -- for example,

         Compute (fun x:bool => 3 + 4)

    yields [fun x:bool => 7].

    Most real-world functional programming languages make the second
    choice -- reduction of a function's body only begins when the
    function is actually applied to an argument.  We also make the
    second choice here. *)
*)
(** 三番目に、関数抽象については選択肢があります:
 
      - [\x:T.t1] が値であるのは、[t1]が値であるときのみである、とすることができます。
        つまり、関数の本体が(どのような引数に適用されるかわからない状態で可能な限り)簡約済みであるときのみ、ということです。
 
      - あるいは、[\x:T.t1] は常に値である、とすることもできます。
        [t1]が値であるかどうかに関係なく、です。
        言いかえると、簡約は関数抽象で止まる、とすることです。
 
    ここで使っている Coq での式の評価は最初の選択肢を取っています。例えば、
[[
         Compute (fun x:bool => 3 + 4) 
]]
    は [fun x:bool => 7] となります。
 
    よく使われる関数型プログラミング言語のほとんどは、第二の選択肢を取っています。
    つまり、関数の本体の簡約は、関数が実際に引数に適用されたときにのみ開始されます。
    ここでは、同様に第二の選択肢を選びます。 *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (tabs x T t)
  | v_true :
      value ttrue
  | v_false :
      value tfalse.

Hint Constructors value.

(*
(** Finally, we must consider what constitutes a _complete_ program.

    Intuitively, a "complete program" must not refer to any undefined
    variables.  We'll see shortly how to define the _free_ variables
    in a STLC term.  A complete program is _closed_ -- that is, it
    contains no free variables.

    (Conversely, a term with free variables is often called an _open 
    term_.) 

    Having made the choice not to reduce under abstractions, we don't
    need to worry about whether variables are values, since we'll
    always be reducing programs "from the outside in," and that means
    the [step] relation will always be working with closed terms.  *)
*)
(** 最後に、「完全な(_complete_)」プログラムの性質について考えます。
 
    直観的には、「完全なプログラム」は未定義の変数を参照しないでしょう。
    すぐにSTLC項について「自由(_free_)」変数の定義を見ますが、完全なプログラムは「閉じた(_closed_)」もの、つまり自由変数を含まないものです。
 
    （逆に、自由変数を含む項は「開いた項(_open term_)」と呼ばれることもあります。）
 
    関数抽象の中を簡約することを選択しなかったため、変数が値であるかをどうかを心配する必要はなくなります。
    なぜなら、プログラムの簡約は常に「外側から内側に」行われ、[step]関係は常に閉じた項だけを対象とするからです。 *)

(* ================================================================= *)
(*
(** ** Substitution *)
*)
(** ** 置換 *)

(*
(** Now we come to the heart of the STLC: the operation of
    substituting one term for a variable in another term.  This
    operation is used below to define the operational semantics of
    function application, where we will need to substitute the
    argument term for the function parameter in the function's body.
    For example, we reduce

       (\x:Bool. if x then true else x) false

    to

       if false then true else false

    by substituting [false] for the parameter [x] in the body of the
    function.

    In general, we need to be able to substitute some given term [s]
    for occurrences of some variable [x] in another term [t].  In
    informal discussions, this is usually written [ [x:=s]t ] and
    pronounced "substitute [x] with [s] in [t]." *)
*)
(** これから問題の核心に入ります: 項の変数を別の項で置換する操作です。
    この操作は後で関数適用の操作的意味論を定義するために使います。
    関数適用では、関数本体の中の関数パラメータを引数項で置換することが必要になります。
    例えば、
[[
       (\x:Bool. if x then true else x) false
]]
    を
[[
       if false then true else false
]]
    に簡約するには、関数の本体のパラメータ[x]を[false]で置換することでできます。
 
    一般に、ある項[t]の変数[x]の出現を、与えらえた項[s]で置換できることが必要です。
    非形式的な議論では、通常これを [ [x:=s]t ] と書き、「[t]の[x]を[s]で置換する」と読みます。 *)

(*
(** Here are some examples:

      - [[x:=true] (if x then x else false)] 
           yields [if true then true else false]

      - [[x:=true] x] yields [true]

      - [[x:=true] (if x then x else y)] yields [if true then true else y]

      - [[x:=true] y] yields [y]

      - [[x:=true] false] yields [false] (vacuous substitution)

      - [[x:=true] (\y:Bool. if y then x else false)] 
           yields [\y:Bool. if y then true else false]

      - [[x:=true] (\y:Bool. x)] yields [\y:Bool. true]

      - [[x:=true] (\y:Bool. y)] yields [\y:Bool. y]

      - [[x:=true] (\x:Bool. x)] yields [\x:Bool. x]

    The last example is very important: substituting [x] with [true] in
    [\x:Bool. x] does _not_ yield [\x:Bool. true]!  The reason for
    this is that the [x] in the body of [\x:Bool. x] is _bound_ by the
    abstraction: it is a new, local name that just happens to be
    spelled the same as some global name [x]. *)
*)
(** いくつかの例を示します:
 
      - [[x:=true] (if x then x else false)] は [if true then true else false] となります。
 
      - [[x:=true] x] は [true] となります。
 
      - [[x:=true] (if x then x else y)] は [if true then true else y] となります。
 
      - [[x:=true] y] は [y] となります。
 
      - [[x:=true] false] は [false] となります(何もしない置換です)。
 
      - [[x:=true] (\y:Bool. if y then x else false)] は
        [\y:Bool. if y then true else false] となります。
 
      - [[x:=true] (\y:Bool. x)] は [\y:Bool. true] となります。
 
      - [[x:=true] (\y:Bool. y)] は [\y:Bool. y] となります。
 
      - [[x:=true] (\x:Bool. x)] は [\x:Bool. x] となります。
 
    最後の例はとても重要です。
    [\x:Bool. x] の [x] を [true] で置換したものは、[\x:Bool. true] に「なりません」! 
    理由は、[\x:Bool. x] の本体の [x] は関数抽象で束縛されている(_bound_)からです。
    この[x]は新しいローカルな名前で、たまたまグローバルな名前[x]と同じ綴りであったものです。 *)

(*
(** Here is the definition, informally...

       [x:=s]x               = s
       [x:=s]y               = y                      if x <> y
       [x:=s](\x:T11. t12)   = \x:T11. t12
       [x:=s](\y:T11. t12)   = \y:T11. [x:=s]t12      if x <> y
       [x:=s](t1 t2)         = ([x:=s]t1) ([x:=s]t2)
       [x:=s]true            = true
       [x:=s]false           = false
       [x:=s](if t1 then t2 else t3) =
                       if [x:=s]t1 then [x:=s]t2 else [x:=s]t3
*)
 *)
(** 以下が、非形式的な定義です...
[[
       [x:=s]x               = s 
       [x:=s]y               = y                      if x <> y 
       [x:=s](\x:T11. t12)   = \x:T11. t12 
       [x:=s](\y:T11. t12)   = \y:T11. [x:=s]t12      if x <> y 
       [x:=s](t1 t2)         = ([x:=s]t1) ([x:=s]t2) 
       [x:=s]true            = true 
       [x:=s]false           = false 
       [x:=s](if t1 then t2 else t3) = 
                       if [x:=s]t1 then [x:=s]t2 else [x:=s]t3 
]]
 *)

(*
(** ... and formally: *)
*)
(** ... そして形式的には: *)

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | tvar x' =>
      if beq_id x x' then s else t
  | tabs x' T t1 =>
      tabs x' T (if beq_id x x' then t1 else ([x:=s] t1))
  | tapp t1 t2 =>
      tapp ([x:=s] t1) ([x:=s] t2)
  | ttrue =>
      ttrue
  | tfalse =>
      tfalse
  | tif t1 t2 t3 =>
      tif ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
  end

where "'[' x ':=' s ']' t" := (subst x s t).

(*
(** _Technical note_: Substitution becomes trickier to define if we
    consider the case where [s], the term being substituted for a
    variable in some other term, may itself contain free variables.
    Since we are only interested here in defining the [step] relation
    on closed terms (i.e., terms like [\x:Bool. x] that include
    binders for all of the variables they mention), we can avoid this
    extra complexity here, but it must be dealt with when formalizing
    richer languages. *)
*)
(** 技術的注釈: 置換は、もし[s]、つまり他の項の変数を置換する項が、それ自身に自由変数を含むときを考えると、定義がよりトリッキーなものになります。
    ここで興味があるのは閉じた項（つまり [\x:Bool. x] のように、出現する全ての変数についての束縛子を含む項）についての[step]関係の定義のみなので、そのさらなる複雑さは避けることができます。
    しかし、より表現力の強い言語を形式化する場合には考慮する必要があるでしょう。 *)

(** See, for example, [Aydemir 2008] for further discussion
    of this issue. *)

(** **** Exercise: 3 stars (substi)  *)
(** The definition that we gave above uses Coq's [Fixpoint] facility
    to define substitution as a _function_.  Suppose, instead, we
    wanted to define substitution as an inductive _relation_ [substi].
    We've begun the definition by providing the [Inductive] header and
    one of the constructors; your job is to fill in the rest of the
    constructors and prove that the relation you've defined coincides
    with the function given above. *)

Inductive substi (s:tm) (x:id) : tm -> tm -> Prop :=
  | s_var1 :
      substi s x (tvar x) s
  (* FILL IN HERE *)
.

Hint Constructors substi.

Theorem substi_correct : forall s x t t',
  [x:=s]t = t' <-> substi s x t t'.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(*
(** ** Reduction *)
*)
(** ** 簡約 *)

(*
(** The small-step reduction relation for STLC now follows the
    same pattern as the ones we have seen before.  Intuitively, to
    reduce a function application, we first reduce its left-hand
    side (the function) until it becomes an abstraction; then we
    reduce its right-hand side (the argument) until it is also a
    value; and finally we substitute the argument for the bound
    variable in the body of the abstraction.  This last rule, written
    informally as

      (\x:T.t12) v2 ==> [x:=v2]t12

    is traditionally called "beta-reduction". *)
*)
(** STLCのスモールステップ簡約関係は、これまで見てきたものと同じパターンに従います。
    直観的には、関数適用を簡約するため、最初に左側（関数）を関数値になるまで簡約します。
    次に右側（引数）を値になるまで簡約します。
    そして最後に関数の本体の束縛変数を引数で置換します。
    この最後の規則は、非形式的には次のように書きます:
[[
      (\x:T.t12) v2 ==> [x:=v2]t12
]]
    これは伝統的にベータ簡約("beta-reduction")と呼ばれます。 *)

(*
(** 
                               value v2
                     ----------------------------                   (ST_AppAbs)
                     (\x:T.t12) v2 ==> [x:=v2]t12

                              t1 ==> t1'
                           ----------------                           (ST_App1)
                           t1 t2 ==> t1' t2

                              value v1
                              t2 ==> t2'
                           ----------------                           (ST_App2)
                           v1 t2 ==> v1 t2'
*)
 *)
(**
<<
                               value v2 
                     ----------------------------                   (ST_AppAbs) 
                     (\x:T.t12) v2 ==> [x:=v2]t12 
 
                              t1 ==> t1' 
                           ----------------                           (ST_App1) 
                           t1 t2 ==> t1' t2 
 
                              value v1 
                              t2 ==> t2' 
                           ----------------                           (ST_App2) 
                           v1 t2 ==> v1 t2' 
>>
 *)
(*
(** ... plus the usual rules for booleans:

                    --------------------------------                (ST_IfTrue)
                    (if true then t1 else t2) ==> t1

                    ---------------------------------              (ST_IfFalse)
                    (if false then t1 else t2) ==> t2

                              t1 ==> t1'
         ----------------------------------------------------           (ST_If)
         (if t1 then t2 else t3) ==> (if t1' then t2 else t3)
*)
 *)
(** ...以上に加えて、通常のブール値に関する規則:
<<
                    --------------------------------                (ST_IfTrue) 
                    (if true then t1 else t2) ==> t1 
 
                    ---------------------------------              (ST_IfFalse) 
                    (if false then t1 else t2) ==> t2 
 
                              t1 ==> t1' 
         ----------------------------------------------------           (ST_If) 
         (if t1 then t2 else t3) ==> (if t1' then t2 else t3) 
>>
*)

(** Formally: *)

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
         value v2 ->
         (tapp (tabs x T t12) v2) ==> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
         t1 ==> t1' ->
         tapp t1 t2 ==> tapp t1' t2
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 ==> t2' ->
         tapp v1 t2 ==> tapp v1  t2'
  | ST_IfTrue : forall t1 t2,
      (tif ttrue t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
      (tif tfalse t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tif t1 t2 t3) ==> (tif t1' t2 t3)

where "t1 '==>' t2" := (step t1 t2).

Hint Constructors step.

Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

(* ================================================================= *)
(*
(** ** Examples *)
*)
(** ** 例 *)

(** Example:

      (\x:Bool->Bool. x) (\x:Bool. x) ==>* \x:Bool. x

    i.e.,

      idBB idB ==>* idB
*)

Lemma step_example1 :
  (tapp idBB idB) ==>* idB.
Proof.
  eapply multi_step.
    apply ST_AppAbs.
    apply v_abs.
  simpl.
  apply multi_refl.  Qed.

(** Example:

      (\x:Bool->Bool. x) ((\x:Bool->Bool. x) (\x:Bool. x))
            ==>* \x:Bool. x

    i.e.,

      (idBB (idBB idB)) ==>* idB.
*)

Lemma step_example2 :
  (tapp idBB (tapp idBB idB)) ==>* idB.
Proof.
  eapply multi_step.
    apply ST_App2. auto.
    apply ST_AppAbs. auto.
  eapply multi_step.
    apply ST_AppAbs. simpl. auto.
  simpl. apply multi_refl.  Qed.

(** Example:

      (\x:Bool->Bool. x) 
         (\x:Bool. if x then false else true) 
         true
            ==>* false

    i.e.,

       (idBB notB) ttrue ==>* tfalse.
*)

Lemma step_example3 :
  tapp (tapp idBB notB) ttrue ==>* tfalse.
Proof.
  eapply multi_step.
    apply ST_App1. apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_IfTrue. apply multi_refl.  Qed.

(** Example:

      (\x:Bool -> Bool. x) 
         ((\x:Bool. if x then false else true) true)
            ==>* false

    i.e.,

      idBB (notB ttrue) ==>* tfalse.
*)

Lemma step_example4 :
  tapp idBB (tapp notB ttrue) ==>* tfalse.
Proof.
  eapply multi_step.
    apply ST_App2. auto.
    apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_App2. auto.
    apply ST_IfTrue.
  eapply multi_step.
    apply ST_AppAbs. auto. simpl.
  apply multi_refl.  Qed.

(*
(** We can use the [normalize] tactic defined in the [Types] chapter
    to simplify these proofs. *)
*)
(** [Types]章で定義した[normalize]タクティックを使って、証明を簡単にすることができます。*)

Lemma step_example1' :
  (tapp idBB idB) ==>* idB.
Proof. normalize.  Qed.

Lemma step_example2' :
  (tapp idBB (tapp idBB idB)) ==>* idB.
Proof. normalize. Qed.

Lemma step_example3' :
  tapp (tapp idBB notB) ttrue ==>* tfalse.
Proof. normalize.  Qed.

Lemma step_example4' :
  tapp idBB (tapp notB ttrue) ==>* tfalse.
Proof. normalize.  Qed.

(*
(** **** Exercise: 2 stars (step_example5)  *)
*)
(** **** 練習問題: ★★ (step_example5)  *)
(*
(** Try to do this one both with and without [normalize]. *)
*)
(** 次の証明を[normalize]を使う方法と使わない方法の両方で行いなさい。*)

Lemma step_example5 :
       tapp (tapp idBBBB idBB) idB
  ==>* idB.
Proof.
  (* FILL IN HERE *) Admitted.

Lemma step_example5_with_normalize :
       tapp (tapp idBBBB idBB) idB
  ==>* idB.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(*
(** * Typing *)
*)
(** * 型付け *)

(** Next we consider the typing relation of the STLC. *)

(* ================================================================= *)
(*
(** ** Contexts *)
*)
(** ** コンテキスト *)

(*
(** _Question_: What is the type of the term "[x y]"?

    _Answer_: It depends on the types of [x] and [y]!

    I.e., in order to assign a type to a term, we need to know
    what assumptions we should make about the types of its free
    variables.

    This leads us to a three-place _typing judgment_, informally
    written [Gamma |- t \in T], where [Gamma] is a
    "typing context" -- a mapping from variables to their types. *)
*)
(** 問い: 項 "[x y]" の型は何でしょう？
 
    答え: それは [x] と [y] の型に依存します!
 
    つまり、項に型を付けるためには、その自由変数の型についてどういう仮定をしなければならないかを知る必要があります。
 
    このために、3つのものの間の型付けジャッジメント(_typing judgment_)を用意します。
    これを非形式的には [Gamma |- t \in T] と記述します。
    ここで [Gamma] は「型付けコンテキスト」("typing context")、つまり、変数から型への写像です。 *)

(** Informally, we'll write [Gamma, x:T] for "extend the partial
    function [Gamma] to also map [x] to [T]."  Formally, we use the
    function [extend] to add a binding to a partial map. *)

Definition context := partial_map ty.

(* ================================================================= *)
(*
(** ** Typing Relation *)
*)
(** ** 型付け関係 *)

(*
(** 
                             Gamma x = T
                            --------------                              (T_Var)
                            Gamma |- x \in T

                      Gamma , x:T11 |- t12 \in T12
                     ----------------------------                       (T_Abs)
                     Gamma |- \x:T11.t12 \in T11->T12

                        Gamma |- t1 \in T11->T12
                          Gamma |- t2 \in T11
                        ----------------------                          (T_App)
                         Gamma |- t1 t2 \in T12

                         --------------------                          (T_True)
                         Gamma |- true \in Bool

                        ---------------------                         (T_False)
                        Gamma |- false \in Bool

       Gamma |- t1 \in Bool    Gamma |- t2 \in T    Gamma |- t3 \in T
       --------------------------------------------------------          (T_If)
                  Gamma |- if t1 then t2 else t3 \in T


    We can read the three-place relation [Gamma |- t \in T] as:
    "to the term [t] we can assign the type [T] using as types for
    the free variables of [t] the ones specified in the context
    [Gamma]." *)
*)
(**
<<
                             Gamma x = T 
                            --------------                              (T_Var) 
                            Gamma |- x \in T 
 
                      Gamma , x:T11 |- t12 \in T12 
                     ----------------------------                       (T_Abs) 
                     Gamma |- \x:T11.t12 \in T11->T12 
 
                        Gamma |- t1 \in T11->T12 
                          Gamma |- t2 \in T11 
                        ----------------------                          (T_App) 
                         Gamma |- t1 t2 \in T12 
 
                         --------------------                          (T_True) 
                         Gamma |- true \in Bool 
 
                        ---------------------                         (T_False) 
                        Gamma |- false \in Bool 
 
       Gamma |- t1 \in Bool    Gamma |- t2 \in T    Gamma |- t3 \in T 
       --------------------------------------------------------          (T_If) 
                  Gamma |- if t1 then t2 else t3 \in T 
>> 
 
    三項関係 [Gamma |- t \in T] は次のような意味があります:
    「項 [t] について、 [t] 内の自由変数の型を文脈 [Gamma] によって決定した場合、型 [T] が割り当てられる。」 *)

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- tvar x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      update Gamma x T11 |- t12 \in T12 ->
      Gamma |- tabs x T11 t12 \in TArrow T11 T12
  | T_App : forall T11 T12 Gamma t1 t2,
      Gamma |- t1 \in TArrow T11 T12 ->
      Gamma |- t2 \in T11 ->
      Gamma |- tapp t1 t2 \in T12
  | T_True : forall Gamma,
       Gamma |- ttrue \in TBool
  | T_False : forall Gamma,
       Gamma |- tfalse \in TBool
  | T_If : forall t1 t2 t3 T Gamma,
       Gamma |- t1 \in TBool ->
       Gamma |- t2 \in T ->
       Gamma |- t3 \in T ->
       Gamma |- tif t1 t2 t3 \in T

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.

(* ================================================================= *)
(*
(** ** Examples *)
*)
(** ** 例 *)

Example typing_example_1 :
  empty |- tabs x TBool (tvar x) \in TArrow TBool TBool.
Proof.
  apply T_Abs. apply T_Var. reflexivity.  Qed.

(*
(** Note that since we added the [has_type] constructors to the hints
    database, auto can actually solve this one immediately. *)
*)
(** なお、[has_type]のコンストラクタをヒントデータベースに追加したことから、
    auto でこれを直接解けます。*)

Example typing_example_1' :
  empty |- tabs x TBool (tvar x) \in TArrow TBool TBool.
Proof. auto.  Qed.

(*
(** Another example:

       empty |- \x:A. \y:A->A. y (y x))
             \in A -> (A->A) -> A.
*)
 *)
(** 他の例:
[[
       empty |- \x:A. \y:A->A. y (y x)) 
             \in A -> (A->A) -> A 
]]
 *)

Example typing_example_2 :
  empty |-
    (tabs x TBool
       (tabs y (TArrow TBool TBool)
          (tapp (tvar y) (tapp (tvar y) (tvar x))))) \in
    (TArrow TBool (TArrow (TArrow TBool TBool) TBool)).
Proof with auto using update_eq.
  apply T_Abs.
  apply T_Abs.
  eapply T_App. apply T_Var...
  eapply T_App. apply T_Var...
  apply T_Var...
Qed.

(*
(** **** Exercise: 2 stars, optional (typing_example_2_full)  *)
*)
(** **** 練習問題: ★★, optional (typing_example_2_full)  *)
(*
(** Prove the same result without using [auto], [eauto], or
    [eapply] (or [...]). *)
*)
(** [auto]、[eauto]、[eapply] （またはタクティックの後ろに付ける[...]）を使わずに同じ結果を証明しなさい。 *)

Example typing_example_2_full :
  empty |-
    (tabs x TBool
       (tabs y (TArrow TBool TBool)
          (tapp (tvar y) (tapp (tvar y) (tvar x))))) \in
    (TArrow TBool (TArrow (TArrow TBool TBool) TBool)).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*
(** **** Exercise: 2 stars (typing_example_3)  *)
*)
(** **** 練習問題: ★★ (typing_example_3)  *)
(*
(** Formally prove the following typing derivation holds: *)
*)
(** 次の型付けが成立することを形式的に証明しなさい: *)
(*
(** 
       empty |- \x:Bool->B. \y:Bool->Bool. \z:Bool.
                   y (x z)
             \in T.
*)
 *)
(**  
[[
       empty |- \x:Bool->B. \y:Bool->Bool. \z:Bool. 
                   y (x z) 
             \in T 
]]
 *)

Example typing_example_3 :
  exists T,
    empty |-
      (tabs x (TArrow TBool TBool)
         (tabs y (TArrow TBool TBool)
            (tabs z TBool
               (tapp (tvar y) (tapp (tvar x) (tvar z)))))) \in
      T.
Proof with auto.
  (* FILL IN HERE *) Admitted.
(** [] *)

(*
(** We can also show that terms are _not_ typable.  For example, let's
    formally check that there is no typing derivation assigning a type
    to the term [\x:Bool. \y:Bool, x y] -- i.e.,

    ~ exists T,
        empty |- \x:Bool. \y:Bool, x y \in T.
*)
 *)
(** 項が「型付けできない」ことを証明することもできます。
    例えば [\x:Bool. \y:Bool, x y] に型をつける型付けが存在しないこと、つまり、
[[
    ~ exists T, 
        empty |- \x:Bool. \y:Bool, x y \in T 
]]
    を形式的にチェックしましょう。
 *)

Example typing_nonexample_1 :
  ~ exists T,
      empty |-
        (tabs x TBool
            (tabs y TBool
               (tapp (tvar x) (tvar y)))) \in
        T.
Proof.
  intros Hc. inversion Hc.
  (* The [clear] tactic is useful here for tidying away bits of
     the context that we're not going to need again. *)
  inversion H. subst. clear H.
  inversion H5. subst. clear H5.
  inversion H4. subst. clear H4.
  inversion H2. subst. clear H2.
  inversion H5. subst. clear H5.
  inversion H1.  Qed.

(*
(** **** Exercise: 3 stars, optional (typing_nonexample_3)  *)
*)
(** **** 練習問題: ★★★, optional (typing_nonexample_3)  *)
(*
(** Another nonexample:

    ~ (exists S, exists T,
          empty |- \x:S. x x \in T).
*)
 *)
(** 別の、型を持たない例:
[[
    ~ (exists S, exists T, 
          empty |- \x:S. x x \in T) 
]]
 *)

Example typing_nonexample_3 :
  ~ (exists S, exists T,
        empty |-
          (tabs x S
             (tapp (tvar x) (tvar x))) \in
          T).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

End STLC.

(** $Date: 2017-08-25 14:01:35 -0400 (Fri, 25 Aug 2017) $ *)

