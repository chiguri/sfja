(** * Stlc: 単純型付きラムダ計算 *)
(* begin hide *)
(** * Stlc: The Simply Typed Lambda-Calculus *)
(* end hide *)

(* begin hide *)
(** The simply typed lambda-calculus (STLC) is a tiny core
    calculus embodying the key concept of _functional abstraction_,
    which shows up in pretty much every real-world programming
    language in some form (functions, procedures, methods, etc.).

    We will follow exactly the same pattern as in the previous chapter
    when formalizing this calculus (syntax, small-step semantics,
    typing rules) and its main properties (progress and preservation).
    The new technical challenges arise from the mechanisms of
    _variable binding_ and _substitution_.  It will take some work to
    deal with these. *)
(* end hide *)
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
From Coq Require Import Strings.String.
From PLF Require Import Maps.
From PLF Require Import Smallstep.

(* ################################################################# *)
(* begin hide *)
(** * Overview *)
(* end hide *)
(** ** 概観 *)

(* begin hide *)
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
    formalize it below). 

       t ::= x                         variable
           | \x:T1.t2                  abstraction
           | t1 t2                     application
           | tru                       constant true
           | fls                       constant false
           | test t1 then t2 else t3   conditional
*)
(* end hide *)
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
    （まずは非形式的BNF記法で書き出します。後に形式化します。）
[[
       t ::= x                         variable 
           | \x:T1.t2                  abstraction 
           | t1 t2                     application 
           | tru                       constant true 
           | fls                       constant false 
           | test t1 then t2 else t3   conditional 
]]
 *)

(* begin hide *)
(** The [\] symbol in a function abstraction [\x:T.t] is generally
    written as a Greek letter "lambda" (hence the name of the
    calculus).  The variable [x] is called the _parameter_ to the
    function; the term [t] is its _body_.  The annotation [:T1]
    specifies the type of arguments that the function can be applied
    to. *)
(* 訳注：[:T1]は[:T]のミス？ *)
(* end hide *)
(** 関数抽象 [\x:T.t] の [\]記号はよくギリシャ文字のラムダ(λ)で記述されます（これがラムダ計算の名前の由来です）（訳注：日本語環境では円マークに見えることがあります）。
    変数[x]は関数のパラメータ(_parameter_)、項[t]は関数の本体(_body_)と呼ばれます。
    付記された [:T] は関数が適用される引数の型を定めます。 *)

(* begin hide *)
(** Some examples:

      - [\x:Bool. x]

        The identity function for booleans.

      - [(\x:Bool. x) tru]

        The identity function for booleans, applied to the boolean [tru].

      - [\x:Bool. test x then fls else tru]

        The boolean "not" function.

      - [\x:Bool. tru]

        The constant function that takes every (boolean) argument to
        [tru]. 
      - [\x:Bool. \y:Bool. x]

        A two-argument function that takes two booleans and returns
        the first one.  (As in Coq, a two-argument function is really
        a one-argument function whose body is also a one-argument
        function.)

      - [(\x:Bool. \y:Bool. x) fls tru]

        A two-argument function that takes two booleans and returns
        the first one, applied to the booleans [fls] and [tru].

        As in Coq, application associates to the left -- i.e., this
        expression is parsed as [((\x:Bool. \y:Bool. x) fls) tru].

      - [\f:Bool->Bool. f (f tru)]

        A higher-order function that takes a _function_ [f] (from
        booleans to booleans) as an argument, applies [f] to [tru],
        and applies [f] again to the result.

      - [(\f:Bool->Bool. f (f tru)) (\x:Bool. fls)]

        The same higher-order function, applied to the constantly
        [fls] function. *)
(* end hide *)
(** 例をいくつか:
 
      - [\x:Bool. x] 
 
        ブール値の恒等関数。
 
      - [(\x:Bool. x) tru] 
 
        ブール値[tru]に適用された、ブール値の恒等関数。
 
      - [\x:Bool. test x then fls else tru] 
 
        ブール値の否定(not)関数。
 
      - [\x:Bool. tru] 
 
        すべての(ブール値の)引数に対して[tru]を返す定数関数。
 
      - [\x:Bool. \y:Bool. x] 
 
        2つのブール値をとり、最初のものを返す2引数関数。
        （Coqと同様、2引数関数は、実際には本体が1引数関数である1引数関数です。）
 
      - [(\x:Bool. \y:Bool. x) fls tru] 
 
        2つのブール値をとり、最初のものを返す2引数関数を、ブール値[fls]と[tru]
        に適用したもの。
 
        Coqと同様、関数適用は左結合です。つまり、この式は
        [((\x:Bool. \y:Bool. x) fls) tru] と構文解析されます。
 
      - [\f:Bool->Bool. f (f tru)] 
 
        （ブール値からブール値への）「関数」[f]を引数にとる高階関数。
        この高階関数は、[f]を[tru]に適用し、その結果にさらに[f]を適用します。
 
      - [(\f:Bool->Bool. f (f tru)) (\x:Bool. fls)] 
 
        上記高階関数を、常に[fls]を返す定数関数に適用したもの。 *)

(* begin hide *)
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
    boolean constants [tru] and [fls] as well as more complex
    computations that yield booleans, plus _arrow types_ that classify
    functions. 

      T ::= Bool
          | T -> T

    For example:

      - [\x:Bool. fls] has type [Bool->Bool]

      - [\x:Bool. x] has type [Bool->Bool]

      - [(\x:Bool. x) tru] has type [Bool]

      - [\x:Bool. \y:Bool. x] has type [Bool->Bool->Bool]
                              (i.e., [Bool -> (Bool->Bool)])

      - [(\x:Bool. \y:Bool. x) fls] has type [Bool->Bool]

      - [(\x:Bool. \y:Bool. x) fls tru] has type [Bool] *)
(* end hide *)
(** 最後のいくつかの例で示されたように、STLCは高階(_higher-order_)関数の言語です。
    他の関数を引数として取る関数や、結果として他の関数を返す関数を書き下すことができます。
 
    STLCは、名前を持つ(_named_)関数を定義する基本構文を何も持っていません。
    すべての関数は「無名」("anonymous")です。
    後の[MoreStlc]章で、簡単にこの体系に名前を持つ関数を追加できることを見ます。
    実のところ、基本的な命名と束縛の機構はまったく同じです。
 
    STLCの型には[Bool]が含まれます。
    この型はブール定数[tru]と[fls]、および結果がブール値になるより複雑な計算の型です。
    その他に、関数の型である「関数型」(_arrow types_)があります。
[[
      T ::= Bool 
          | T -> T 
]]
    例えば:
 
      - [\x:Bool. fls] は型 [Bool->Bool] を持ちます。
 
      - [\x:Bool. x] は型 [Bool->Bool] を持ちます。
 
      - [(\x:Bool. x) tru] は型 [Bool] を持ちます。
 
      - [\x:Bool. \y:Bool. x] は型 [Bool->Bool->Bool]
        （つまり [Bool -> (Bool->Bool)]）を持ちます。
 
      - [(\x:Bool. \y:Bool. x) fls] は型 [Bool->Bool] を持ちます。
 
      - [(\x:Bool. \y:Bool. x) fls tru] は型 [Bool] を持ちます。 *)

(* ################################################################# *)
(* begin hide *)
(** * Syntax *)
(* end hide *)
(** * 構文 *)

(** We next formalize the syntax of the STLC. *)

Module STLC.

(* ================================================================= *)
(* begin hide *)
(** ** Types *)
(* end hide *)
(** ** 型 *)

Inductive ty : Type :=
  | Bool  : ty
  | Arrow : ty -> ty -> ty.

(* ================================================================= *)
(* begin hide *)
(** ** Terms *)
(* end hide *)
(** ** 項 *)

Inductive tm : Type :=
  | var : string -> tm
  | app : tm -> tm -> tm
  | abs : string -> ty -> tm -> tm
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm.

(* begin hide *)
(** Note that an abstraction [\x:T.t] (formally, [abs x T t]) is
    always annotated with the type [T] of its parameter, in contrast
    to Coq (and other functional languages like ML, Haskell, etc.),
    which use type inference to fill in missing annotations.  We're
    not considering type inference here. *)
(* end hide *)
(** この中では、関数抽象 [\x:T.t] （形式的には [abs x T t]）には常にパラメータの型[T]が付記されます。
    これは Coq（あるいは他のML、Haskellといった関数型言語）のように、型推論(type inference)によって補うものと対照的です。
    ここでは型推論は考えません。 *)

(* begin hide *)
(** Some examples... *)
(* end hide *)
(** いくつかの例... *)

Open Scope string_scope.

Definition x := "x".
Definition y := "y".
Definition z := "z".

Hint Unfold x.
Hint Unfold y.
Hint Unfold z.

(** [idB = \x:Bool. x] *)

Notation idB :=
  (abs x Bool (var x)).

(** [idBB = \x:Bool->Bool. x] *)

Notation idBB :=
  (abs x (Arrow Bool Bool) (var x)).

(** [idBBBB = \x:(Bool->Bool) -> (Bool->Bool). x] *)

Notation idBBBB :=
  (abs x (Arrow (Arrow Bool Bool)
                      (Arrow Bool Bool))
    (var x)).

(** [k = \x:Bool. \y:Bool. x] *)

Notation k := (abs x Bool (abs y Bool (var x))).

(** [notB = \x:Bool. test x then fls else tru] *)

Notation notB := (abs x Bool (test (var x) fls tru)).

(* begin hide *)
(** (We write these as [Notation]s rather than [Definition]s to make
    things easier for [auto].) *)
(* end hide *)
(** （これらを[Definition]ではなく[Notation]とすることで、[auto]に扱いやすくしています。） *)

(* ################################################################# *)
(* begin hide *)
(** * Operational Semantics *)
(* end hide *)
(** * 操作的意味論 *)

(* begin hide *)
(** To define the small-step semantics of STLC terms, we begin,
    as always, by defining the set of values.  Next, we define the
    critical notions of _free variables_ and _substitution_, which are
    used in the reduction rule for application expressions.  And
    finally we give the small-step relation itself. *)
(* end hide *)
(** STLC項のスモールステップ意味論を定義するために、いつものように、値の集合を定義することから始めます。
    次に、自由変数(_free variables_)と置換(_substitution_)という、重大な概念を定義します。
    これらは関数適用式の簡約規則に使われます。
    そして最後に、スモールステップ関係自体を与えます。 *)

(* ================================================================= *)
(* begin hide *)
(** ** Values *)
(* end hide *)
(** ** 値 *)

(* begin hide *)
(** To define the values of the STLC, we have a few cases to consider.

    First, for the boolean part of the language, the situation is
    clear: [tru] and [fls] are the only values.  A [test] expression
    is never a value. *)
(* end hide *)
(** STLCの値を定義するために、いくつかの場合を考えなければなりません。
 
    最初に、言語のブール値については、状況は明確です:
    [tru]と[fls]だけが値です。[test]式は決して値ではありません。 *)

(* begin hide *)
(** Second, an application is not a value: it represents a function
    being invoked on some argument, which clearly still has work left
    to do. *)
(* end hide *)
(** 二番目に、関数適用は値ではありません。
    関数適用は関数が何らかの引数に対して呼ばれたことを表しているのですから、
    明らかにこれからやることが残っています。 *)

(* begin hide *)
(** Third, for abstractions, we have a choice:

      - We can say that [\x:T. t] is a value only when [t] is a
        value -- i.e., only if the function's body has been
        reduced (as much as it can be without knowing what argument it
        is going to be applied to).

      - Or we can say that [\x:T. t] is always a value, no matter
        whether [t] is one or not -- in other words, we can say that
        reduction stops at abstractions.

    Our usual way of evaluating expressions in Coq makes the first
    choice -- for example,

         Compute (fun x:bool => 3 + 4)

    yields:

          fun x:bool => 7

    Most real-world functional programming languages make the second
    choice -- reduction of a function's body only begins when the
    function is actually applied to an argument.  We also make the
    second choice here. *)
(* end hide *)
(** 三番目に、関数抽象については選択肢があります:
 
      - [\x:T.t] が値であるのは、[t]が値であるときのみである、とすることができます。
        つまり、関数の本体が(どのような引数に適用されるかわからない状態で可能な限り)簡約済みであるときのみ、ということです。
 
      - あるいは、[\x:T.t] は常に値である、とすることもできます。
        [t]が値であるかどうかに関係なく、です。
        言いかえると、簡約は関数抽象で止まる、とすることです。
 
    ここで使っている Coq での式の評価は最初の選択肢を取っています。例えば、
[[
         Compute (fun x:bool => 3 + 4) 
]]
    は
[[
          fun x:bool => 7
]]
    となります。
 
    よく使われる関数型プログラミング言語のほとんどは、第二の選択肢を取っています。
    つまり、関数の本体の簡約は、関数が実際に引数に適用されたときにのみ開始されます。
    ここでは、同様に第二の選択肢を選びます。 *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T t,
      value (abs x T t)
  | v_tru :
      value tru
  | v_fls :
      value fls.

Hint Constructors value.

(* begin hide *)
(** Finally, we must consider what constitutes a _complete_ program.

    Intuitively, a "complete program" must not refer to any undefined
    variables.  We'll see shortly how to define the _free_ variables
    in a STLC term.  A complete program is _closed_ -- that is, it
    contains no free variables.

    (Conversely, a term with free variables is often called an _open
    term_.) *)
(* end hide *)
(** 最後に、「完全な(_complete_)」プログラムの性質について考えます。
 
    直観的には、「完全なプログラム」は未定義の変数を参照しないでしょう。
    すぐにSTLC項について「自由(_free_)」変数の定義を見ますが、完全なプログラムは「閉じた(_closed_)」もの、つまり自由変数を含まないものです。
 
    （逆に、自由変数を含む項は「開いた項(_open term_)」と呼ばれることもあります。） *)

(* begin hide *)
(** Having made the choice not to reduce under abstractions, we don't
    need to worry about whether variables are values, since we'll
    always be reducing programs "from the outside in," and that means
    the [step] relation will always be working with closed terms.  *)
(* end hide *)
(** 関数抽象の中を簡約することを選択しなかったため、変数が値であるかをどうかを心配する必要はなくなります。
    なぜなら、プログラムの簡約は常に「外側から内側に」行われ、[step]関係は常に閉じた項だけを対象とするからです。 *)

(* ================================================================= *)
(* begin hide *)
(** ** Substitution *)
(* end hide *)
(** ** 置換 *)

(* begin hide *)
(** Now we come to the heart of the STLC: the operation of
    substituting one term for a variable in another term.  This
    operation is used below to define the operational semantics of
    function application, where we will need to substitute the
    argument term for the function parameter in the function's body.
    For example, we reduce

       (\x:Bool. test x then tru else x) fls

    to

       test fls then tru else fls

    by substituting [fls] for the parameter [x] in the body of the
    function.

    In general, we need to be able to substitute some given term [s]
    for occurrences of some variable [x] in another term [t].  In
    informal discussions, this is usually written [ [x:=s]t ] and
    pronounced "substitute [s] for [x] in [t]." *)
(* end hide *)
(** これから問題の核心に入ります: 項の変数を別の項で置換する操作です。
    この操作は後で関数適用の操作的意味論を定義するために使います。
    関数適用では、関数本体の中の関数パラメータを引数項で置換することが必要になります。
    例えば、
[[
       (\x:Bool. test x then tru else x) fls 
]]
    を
[[
       test fls then tru else fls 
]]
    に簡約するには、関数の本体のパラメータ[x]を[fls]で置換することでできます。
 
    一般に、ある項[t]の変数[x]の出現を、与えらえた項[s]で置換できることが必要です。
    非形式的な議論では、通常これを [ [x:=s]t ] と書き、「[t]の[x]を[s]で置換する」と読みます。 *)

(* begin hide *)
(** Here are some examples:

      - [[x:=tru] (test x then x else fls)]
           yields [test tru then tru else fls]

      - [[x:=tru] x] yields [tru]

      - [[x:=tru] (test x then x else y)] yields [test tru then tru else y]

      - [[x:=tru] y] yields [y]

      - [[x:=tru] fls] yields [fls] (vacuous substitution)

      - [[x:=tru] (\y:Bool. test y then x else fls)]
           yields [\y:Bool. test y then tru else fls]

      - [[x:=tru] (\y:Bool. x)] yields [\y:Bool. tru]

      - [[x:=tru] (\y:Bool. y)] yields [\y:Bool. y]

      - [[x:=tru] (\x:Bool. x)] yields [\x:Bool. x]

    The last example is very important: substituting [x] with [tru] in
    [\x:Bool. x] does _not_ yield [\x:Bool. tru]!  The reason for
    this is that the [x] in the body of [\x:Bool. x] is _bound_ by the
    abstraction: it is a new, local name that just happens to be
    spelled the same as some global name [x]. *)
(* end hide *)
(** いくつかの例を示します:
 
      - [[x:=tru] (test x then x else fls)] は [test tru then tru else fls] となります。
 
      - [[x:=tru] x] は [tru] となります。
 
      - [[x:=tru] (test x then x else y)] は [test tru then tru else y] となります。
 
      - [[x:=tru] y] は [y] となります。
 
      - [[x:=tru] fls] は [fls] となります(何もしない置換です)。
 
      - [[x:=tru] (\y:Bool. test y then x else fls)] は
        [\y:Bool. test y then tru else fls] となります。
 
      - [[x:=tru] (\y:Bool. x)] は [\y:Bool. tru] となります。
 
      - [[x:=tru] (\y:Bool. y)] は [\y:Bool. y] となります。
 
      - [[x:=tru] (\x:Bool. x)] は [\x:Bool. x] となります。
 
    最後の例はとても重要です。
    [\x:Bool. x] の [x] を [tru] で置換したものは、[\x:Bool. tru] に「なりません」! 
    理由は、[\x:Bool. x] の本体の [x] は関数抽象で束縛されている(_bound_)からです。
    この[x]は新しいローカルな名前で、たまたまグローバルな名前[x]と同じ綴りであったものです。 *)

(* begin hide *)
(** Here is the definition, informally...

       [x:=s]x               = s
       [x:=s]y               = y                     if x <> y
       [x:=s](\x:T11. t12)   = \x:T11. t12
       [x:=s](\y:T11. t12)   = \y:T11. [x:=s]t12     if x <> y
       [x:=s](t1 t2)         = ([x:=s]t1) ([x:=s]t2)
       [x:=s]tru             = tru
       [x:=s]fls             = fls
       [x:=s](test t1 then t2 else t3) =
              test [x:=s]t1 then [x:=s]t2 else [x:=s]t3
*)
(* end hide *)
(** 以下が、非形式的な定義です...
[[
       [x:=s]x               = s 
       [x:=s]y               = y                     if x <> y 
       [x:=s](\x:T11. t12)   = \x:T11. t12 
       [x:=s](\y:T11. t12)   = \y:T11. [x:=s]t12     if x <> y 
       [x:=s](t1 t2)         = ([x:=s]t1) ([x:=s]t2) 
       [x:=s]tru             = tru 
       [x:=s]fls             = fls 
       [x:=s](test t1 then t2 else t3) = 
              test [x:=s]t1 then [x:=s]t2 else [x:=s]t3 
]]
 *)

(* begin hide *)
(** ... and formally: *)
(* end hide *)
(** ... そして形式的には: *)

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | var x' =>
      if eqb_string x x' then s else t
  | abs x' T t1 =>
      abs x' T (if eqb_string x x' then t1 else ([x:=s] t1))
  | app t1 t2 =>
      app ([x:=s] t1) ([x:=s] t2)
  | tru =>
      tru
  | fls =>
      fls
  | test t1 t2 t3 =>
      test ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
  end

where "'[' x ':=' s ']' t" := (subst x s t).

(* begin hide *)
(** _Technical note_: Substitution becomes trickier to define if we
    consider the case where [s], the term being substituted for a
    variable in some other term, may itself contain free variables.
    Since we are only interested here in defining the [step] relation
    on _closed_ terms (i.e., terms like [\x:Bool. x] that include
    binders for all of the variables they mention), we can sidestep this
    extra complexity, but it must be dealt with when formalizing
    richer languages. *)
(* end hide *)
(** 技術的注釈: 置換は、もし[s]、つまり他の項の変数を置換する項が、それ自身に自由変数を含むときを考えると、定義がよりトリッキーなものになります。
    ここで興味があるのは「閉じた(_closed_)」項（つまり [\x:Bool. x] のように、出現する全ての変数についての束縛子を含む項）についての[step]関係の定義のみなので、そのさらなる複雑さは避けることができます。
    しかし、より表現力の強い言語を形式化する場合には考慮する必要があるでしょう。 *)

(** For example, using the definition of substitution above to
    substitute the _open_ term [s = \x:Bool. r], where [r] is a _free_
    reference to some global resource, for the variable [z] in the
    term [t = \r:Bool. z], where [r] is a bound variable, we would get
    [\r:Bool. \x:Bool. r], where the free reference to [r] in [s] has
    been "captured" by the binder at the beginning of [t].

    Why would this be bad?  Because it violates the principle that the
    names of bound variables do not matter.  For example, if we rename
    the bound variable in [t], e.g., let [t' = \w:Bool. z], then
    [[x:=s]t'] is [\w:Bool. \x:Bool. r], which does not behave the
    same as [[x:=s]t = \r:Bool. \x:Bool. r].  That is, renaming a
    bound variable changes how [t] behaves under substitution. *)

(** See, for example, [Aydemir 2008] (in Bib.v) for further discussion
    of this issue. *)

(** **** Exercise: 3 stars, standard (substi_correct)  

    The definition that we gave above uses Coq's [Fixpoint] facility
    to define substitution as a _function_.  Suppose, instead, we
    wanted to define substitution as an inductive _relation_ [substi].
    We've begun the definition by providing the [Inductive] header and
    one of the constructors; your job is to fill in the rest of the
    constructors and prove that the relation you've defined coincides
    with the function given above. *)

Inductive substi (s : tm) (x : string) : tm -> tm -> Prop :=
  | s_var1 :
      substi s x (var x) s
  (* FILL IN HERE *)
.

Hint Constructors substi.

Theorem substi_correct : forall s x t t',
  [x:=s]t = t' <-> substi s x t t'.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(* begin hide *)
(** ** Reduction *)
(* end hide *)
(** ** 簡約 *)

(* begin hide *)
(** The small-step reduction relation for STLC now follows the
    same pattern as the ones we have seen before.  Intuitively, to
    reduce a function application, we first reduce its left-hand
    side (the function) until it becomes an abstraction; then we
    reduce its right-hand side (the argument) until it is also a
    value; and finally we substitute the argument for the bound
    variable in the body of the abstraction.  This last rule, written
    informally as

      (\x:T.t12) v2 --> [x:=v2]t12

    is traditionally called _beta-reduction_. *)
(* end hide *)
(** STLCのスモールステップ簡約関係は、これまで見てきたものと同じパターンに従います。
    直観的には、関数適用を簡約するため、最初に左側（関数）を関数値になるまで簡約します。
    次に右側（引数）を値になるまで簡約します。
    そして最後に関数の本体の束縛変数を引数で置換します。
    この最後の規則は、非形式的には次のように書きます:
[[
      (\x:T.t12) v2 --> [x:=v2]t12
]]
    これは伝統的にベータ簡約(_beta-reduction_)と呼ばれます。 *)

(* begin hide *)
(** 
                               value v2
                     ----------------------------                   (ST_AppAbs)
                     (\x:T.t12) v2 --> [x:=v2]t12

                              t1 --> t1'
                           ----------------                           (ST_App1)
                           t1 t2 --> t1' t2

                              value v1
                              t2 --> t2'
                           ----------------                           (ST_App2)
                           v1 t2 --> v1 t2'

    ... plus the usual rules for conditionals:

                    --------------------------------               (ST_TestTru)
                    (test tru then t1 else t2) --> t1

                    ---------------------------------              (ST_TestFls)
                    (test fls then t1 else t2) --> t2

                             t1 --> t1'
      --------------------------------------------------------     (ST_Test)
      (test t1 then t2 else t3) --> (test t1' then t2 else t3)
*)
(* end hide *)
(**
<<
                               value v2 
                     ----------------------------                   (ST_AppAbs) 
                     (\x:T.t12) v2 --> [x:=v2]t12 
 
                              t1 --> t1' 
                           ----------------                           (ST_App1) 
                           t1 t2 --> t1' t2 
 
                              value v1 
                              t2 --> t2' 
                           ----------------                           (ST_App2) 
                           v1 t2 --> v1 t2' 
>>
    ...以上に加えて、通常の条件文に関する規則:
<<
                    --------------------------------               (ST_TestTru) 
                    (test tru then t1 else t2) --> t1 
 
                    ---------------------------------              (ST_TestFls) 
                    (test fls then t1 else t2) --> t2 
 
                             t1 --> t1' 
      --------------------------------------------------------     (ST_Test) 
      (test t1 then t2 else t3) --> (test t1' then t2 else t3) 
>>
*)

(** Formally: *)

Reserved Notation "t1 '-->' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T t12 v2,
         value v2 ->
         (app (abs x T t12) v2) --> [x:=v2]t12
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         app t1 t2 --> app t1' t2
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         app v1 t2 --> app v1  t2'
  | ST_TestTru : forall t1 t2,
      (test tru t1 t2) --> t1
  | ST_TestFls : forall t1 t2,
      (test fls t1 t2) --> t2
  | ST_Test : forall t1 t1' t2 t3,
      t1 --> t1' ->
      (test t1 t2 t3) --> (test t1' t2 t3)

where "t1 '-->' t2" := (step t1 t2).

Hint Constructors step.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

(* ================================================================= *)
(* begin hide *)
(** ** Examples *)
(* end hide *)
(** ** 例 *)

(** Example:

      (\x:Bool->Bool. x) (\x:Bool. x) -->* \x:Bool. x

    i.e.,

      idBB idB -->* idB
*)

Lemma step_example1 :
  (app idBB idB) -->* idB.
Proof.
  eapply multi_step.
    apply ST_AppAbs.
    apply v_abs.
  simpl.
  apply multi_refl.  Qed.

(** Example:

      (\x:Bool->Bool. x) ((\x:Bool->Bool. x) (\x:Bool. x))
            -->* \x:Bool. x

    i.e.,

      (idBB (idBB idB)) -->* idB.
*)

Lemma step_example2 :
  (app idBB (app idBB idB)) -->* idB.
Proof.
  eapply multi_step.
    apply ST_App2. auto.
    apply ST_AppAbs. auto.
  eapply multi_step.
    apply ST_AppAbs. simpl. auto.
  simpl. apply multi_refl.  Qed.

(** Example:

      (\x:Bool->Bool. x)
         (\x:Bool. test x then fls else tru)
         tru
            -->* fls

    i.e.,

       (idBB notB) tru -->* fls.
*)

Lemma step_example3 :
  app (app idBB notB) tru -->* fls.
Proof.
  eapply multi_step.
    apply ST_App1. apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_TestTru. apply multi_refl.  Qed.

(** Example:

      (\x:Bool -> Bool. x)
         ((\x:Bool. test x then fls else tru) tru)
            -->* fls

    i.e.,

      idBB (notB tru) -->* fls.

    (Note that this term doesn't actually typecheck; even so, we can
    ask how it reduces.)
*)

Lemma step_example4 :
  app idBB (app notB tru) -->* fls.
Proof.
  eapply multi_step.
    apply ST_App2. auto.
    apply ST_AppAbs. auto. simpl.
  eapply multi_step.
    apply ST_App2. auto.
    apply ST_TestTru.
  eapply multi_step.
    apply ST_AppAbs. auto. simpl.
  apply multi_refl.  Qed.

(* begin hide *)
(** We can use the [normalize] tactic defined in the [Smallstep] chapter
    to simplify these proofs. *)
(* end hide *)
(** [Smallstep]章で定義した[normalize]タクティックを使って、証明を簡単にすることができます。*)

Lemma step_example1' :
  app idBB idB -->* idB.
Proof. normalize.  Qed.

Lemma step_example2' :
  app idBB (app idBB idB) -->* idB.
Proof. normalize. Qed.

Lemma step_example3' :
  app (app idBB notB) tru -->* fls.
Proof. normalize.  Qed.

Lemma step_example4' :
  app idBB (app notB tru) -->* fls.
Proof. normalize.  Qed.

(* begin hide *)
(** **** Exercise: 2 stars, standard (step_example5)  

    Try to do this one both with and without [normalize]. *)
(* end hide *)
(** **** 練習問題: ★★, standard (step_example5)
 
    次の証明を[normalize]を使う方法と使わない方法の両方で行いなさい。*)

Lemma step_example5 :
       app (app idBBBB idBB) idB
  -->* idB.
Proof.
  (* FILL IN HERE *) Admitted.

Lemma step_example5_with_normalize :
       app (app idBBBB idBB) idB
  -->* idB.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################# *)
(* begin hide *)
(** * Typing *)
(* end hide *)
(** * 型付け *)

(** Next we consider the typing relation of the STLC. *)

(* ================================================================= *)
(* begin hide *)
(** ** Contexts *)
(* end hide *)
(** ** コンテキスト *)

(* begin hide *)
(** _Question_: What is the type of the term "[x y]"?

    _Answer_: It depends on the types of [x] and [y]!

    I.e., in order to assign a type to a term, we need to know
    what assumptions we should make about the types of its free
    variables.

    This leads us to a three-place _typing judgment_, informally
    written [Gamma |- t \in T], where [Gamma] is a
    "typing context" -- a mapping from variables to their types. *)
(* end hide *)
(** 問い: 項 "[x y]" の型は何でしょう？
 
    答え: それは [x] と [y] の型に依存します!
 
    つまり、項に型を付けるためには、その自由変数の型についてどういう仮定をしなければならないかを知る必要があります。
 
    このために、3つのものの間の型付けジャッジメント(_typing judgment_)を用意します。
    これを非形式的には [Gamma |- t \in T] と記述します。
    ここで [Gamma] は「型付けコンテキスト」("typing context")、つまり、変数から型への写像です。 *)

(** Following the usual notation for partial maps, we write [(X |->
    T11, Gamma)] for "update the partial function [Gamma] so that it
    maps [x] to [T]." *)

Definition context := partial_map ty.

(* ================================================================= *)
(* begin hide *)
(** ** Typing Relation *)
(* end hide *)
(** ** 型付け関係 *)

(* begin hide *)
(** 
                              Gamma x = T
                            ----------------                            (T_Var)
                            Gamma |- x \in T

                   (x |-> T11 ; Gamma) |- t12 \in T12
                   ----------------------------------                   (T_Abs)
                    Gamma |- \x:T11.t12 \in T11->T12

                        Gamma |- t1 \in T11->T12
                          Gamma |- t2 \in T11
                         ----------------------                         (T_App)
                         Gamma |- t1 t2 \in T12

                         ---------------------                          (T_Tru)
                         Gamma |- tru \in Bool

                         ---------------------                          (T_Fls)
                         Gamma |- fls \in Bool

       Gamma |- t1 \in Bool    Gamma |- t2 \in T    Gamma |- t3 \in T
       --------------------------------------------------------------   (T_Test)
                  Gamma |- test t1 then t2 else t3 \in T

    We can read the three-place relation [Gamma |- t \in T] as:
    "under the assumptions in Gamma, the term [t] has the type [T]." *)
(* end hide *)
(**
<<
                              Gamma x = T 
                            ----------------                            (T_Var) 
                            Gamma |- x \in T 
 
                   (x |-> T11 ; Gamma) |- t12 \in T12 
                   ----------------------------------                   (T_Abs) 
                    Gamma |- \x:T11.t12 \in T11->T12 
 
                        Gamma |- t1 \in T11->T12 
                          Gamma |- t2 \in T11 
                         ----------------------                         (T_App) 
                         Gamma |- t1 t2 \in T12 
 
                         ---------------------                          (T_Tru) 
                         Gamma |- tru \in Bool 
 
                         ---------------------                          (T_Fls) 
                         Gamma |- fls \in Bool 
 
       Gamma |- t1 \in Bool    Gamma |- t2 \in T    Gamma |- t3 \in T 
       --------------------------------------------------------------   (T_Test) 
                  Gamma |- test t1 then t2 else t3 \in T 
>> 
    三項関係 [Gamma |- t \in T] は次のような意味があります:
    「[Gamma] による仮定の下では、項 [t] には型 [T] が割り当てられる。」 *)

Reserved Notation "Gamma '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      Gamma |- var x \in T
  | T_Abs : forall Gamma x T11 T12 t12,
      (x |-> T11 ; Gamma) |- t12 \in T12 ->
      Gamma |- abs x T11 t12 \in Arrow T11 T12
  | T_App : forall T11 T12 Gamma t1 t2,
      Gamma |- t1 \in Arrow T11 T12 ->
      Gamma |- t2 \in T11 ->
      Gamma |- app t1 t2 \in T12
  | T_Tru : forall Gamma,
       Gamma |- tru \in Bool
  | T_Fls : forall Gamma,
       Gamma |- fls \in Bool
  | T_Test : forall t1 t2 t3 T Gamma,
       Gamma |- t1 \in Bool ->
       Gamma |- t2 \in T ->
       Gamma |- t3 \in T ->
       Gamma |- test t1 t2 t3 \in T

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type.

(* ================================================================= *)
(* begin hide *)
(** ** Examples *)
(* end hide *)
(** ** 例 *)

Example typing_example_1 :
  empty |- abs x Bool (var x) \in Arrow Bool Bool.
Proof.
  apply T_Abs. apply T_Var. reflexivity.  Qed.

(* begin hide *)
(** Note that, since we added the [has_type] constructors to the hints
    database, [auto] can actually solve this one immediately. *)
(* end hide *)
(** なお、[has_type]のコンストラクタをヒントデータベースに追加したことから、
    [auto] でこれを直接解けます。*)

Example typing_example_1' :
  empty |- abs x Bool (var x) \in Arrow Bool Bool.
Proof. auto.  Qed.

(* begin hide *)
(** More examples:

       empty |- \x:A. \y:A->A. y (y x)
             \in A -> (A->A) -> A.
*)
(* end hide *)
(** 他の例:
[[
       empty |- \x:A. \y:A->A. y (y x) 
             \in A -> (A->A) -> A. 
]]
 *)

Example typing_example_2 :
  empty |-
    (abs x Bool
       (abs y (Arrow Bool Bool)
          (app (var y) (app (var y) (var x))))) \in
    (Arrow Bool (Arrow (Arrow Bool Bool) Bool)).
Proof with auto using update_eq.
  apply T_Abs.
  apply T_Abs.
  eapply T_App. apply T_Var...
  eapply T_App. apply T_Var...
  apply T_Var...
Qed.

(* begin hide *)
(** **** Exercise: 2 stars, standard, optional (typing_example_2_full)  

    Prove the same result without using [auto], [eauto], or
    [eapply] (or [...]). *)
(* end hide *)
(** **** 練習問題: ★★, standard, optional (typing_example_2_full)
 
    [auto]、[eauto]、[eapply] （またはタクティックの後ろに付ける[...]）を使わずに同じ結果を証明しなさい。 *)

Example typing_example_2_full :
  empty |-
    (abs x Bool
       (abs y (Arrow Bool Bool)
          (app (var y) (app (var y) (var x))))) \in
    (Arrow Bool (Arrow (Arrow Bool Bool) Bool)).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* begin hide *)
(** **** Exercise: 2 stars, standard (typing_example_3)  

    Formally prove the following typing derivation holds: 

    
       empty |- \x:Bool->B. \y:Bool->Bool. \z:Bool.
                   y (x z)
             \in T.
*)
(* end hide *)
(** **** 練習問題: ★★, standard (typing_example_3)
 
    次の型付けが成立することを形式的に証明しなさい:
 
[[
       empty |- \x:Bool->B. \y:Bool->Bool. \z:Bool. 
                   y (x z) 
             \in T. 
]]
 *)

Example typing_example_3 :
  exists T,
    empty |-
      (abs x (Arrow Bool Bool)
         (abs y (Arrow Bool Bool)
            (abs z Bool
               (app (var y) (app (var x) (var z)))))) \in
      T.
Proof with auto.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* begin hide *)
(** We can also show that some terms are _not_ typable.  For example, 
    let's check that there is no typing derivation assigning a type
    to the term [\x:Bool. \y:Bool, x y] -- i.e.,

    ~ exists T,
        empty |- \x:Bool. \y:Bool, x y \in T.
*)
(* end hide *)
(** ある項が「型付けできない」ことを証明することもできます。
    例えば [\x:Bool. \y:Bool, x y] に型をつける型付けが存在しないこと、つまり、
[[
    ~ exists T, 
        empty |- \x:Bool. \y:Bool, x y \in T 
]]
    を形式的にチェックしましょう。 *)

Example typing_nonexample_1 :
  ~ exists T,
      empty |-
        (abs x Bool
            (abs y Bool
               (app (var x) (var y)))) \in
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

(* begin hide *)
(** **** Exercise: 3 stars, standard, optional (typing_nonexample_3)  

    Another nonexample:

    ~ (exists S T,
          empty |- \x:S. x x \in T).
*)
(* end hide *)
(** **** 練習問題: ★★★, standard, optional (typing_nonexample_3)
 
    別の、型を持たない例:
[[
    ~ (exists S, exists T, 
          empty |- \x:S. x x \in T) 
]]
 *)

Example typing_nonexample_3 :
  ~ (exists S T,
        empty |-
          (abs x S
             (app (var x) (var x))) \in
          T).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

End STLC.

(* Thu Feb 7 20:09:24 EST 2019 *)
