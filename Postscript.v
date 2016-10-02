(** * Postscript_J: あとがき *)
(* * Postscript *)

(* * Looking back... *)
(** * ふりかえり... *)

(*  - _Functional programming_
          - "declarative" programming (recursion over persistent data
            structures)
          - higher-order functions
          - polymorphism *)
(**  - 関数プログラミング
          - 「宣言的」プログラミング(永続データ構造上の再帰)
          - 高階関数
          - 多相性 *)

(*
     - _Logic_, the mathematical basis for software engineering:
<<
               logic                        calculus
        --------------------   =   ----------------------------
        software engineering       mechanical/civil engineering
>>

          - inductively defined sets and relations 
          - inductive proofs 
          - proof objects *)
(**
     - 論理学、ソフトウェア工学の数学的基盤:
<<
                論理学                        微積分学
        --------------------   =   ----------------------------
            ソフトウェア工学                  機械/土木工学
>>

          - 帰納的に定義された集合と関係
          - 帰納的証明
          - 証明オブジェクト *)

(*
     - _Coq_, an industrial-strength proof assistant
          - functional core language
          - core tactics
          - automation
*)
(**
     - _Coq_、産業用途に耐え得る証明支援器
          - 関数型のコア言語
          - 基礎となるタクティック
          - 自動化
*)

(**
     - _Foundations of programming languages_ 

           - notations and definitional techniques for precisely specifying
                - abstract syntax
                - operational semantics
                    - big-step style
                    - small-step style
                - type systems

           - program equivalence

           - Hoare logic

           - fundamental metatheory of type systems

              - progress and preservation

           - theory of subtyping
*)
(**
     - プログラミング言語の基礎

           - 以下を精密に定めるための記法と定義法
                - 抽象構文
                - 操作的意味
                    - ビッグステップスタイル
                    - スモールステップスタイル
                - 型システム

           - ホーア論理

           - プログラム同値性

           - 型システムの基本的メタ理論

              - 進行と保存

              - 動的にアロケートされるヒープを持つ言語の型健全性

           - サブタイプ理論
*)

(* ###################################################################### *)
(* * Looking forward... *)
(** * これからの指針... *)

(* Some good places to go for more...

       - Several optional chapters of _Software Foundations_ 

       - Cutting-edge conferences on programming languages and formal
         verification:
            - POPL
            - PLDI
            - OOPSLA
            - ICFP
            - CAV
            - (and many others)

       - More on functional programming
            - Learn You a Haskell for Great Good, by Miran
              Lipovaca (ebook)
            - and many other texts on Haskell, OCaml, Scheme, Scala, ...

       - More on Hoare logic and program verification
            - The Formal Semantics of Programming Languages: An
              Introduction, by Glynn Winskel.  MIT Press, 1993.
            - Many practical verification tools, e.g. Microsoft's
              Boogie system, Java Extended Static Checking, etc.

       - More on the foundations of programming languages:
            - Types and Programming Languages, by Benjamin C. Pierce. MIT
              Press, 2002.
            - Practical Foundations for Programming Languages, by Robert
              Harper.  Forthcoming from MIT Press.  Manuscript available
              from his web page.
            - Foundations for Programming Languages, by John C. Mitchell.
              MIT Press, 1996. 
 
       - More on Coq: 
           - Certified Programming with Dependent Types, by Adam
             Chlipala.  A draft textbook on practical proof
             engineering with Coq, available from his web page.
           - Interactive Theorem Proving and Program Development:
             Coq'Art: The Calculus of Inductive Constructions, by Yves
             Bertot and Pierre Casteran.  Springer-Verlag, 2004.
           - Iron Lambda (http://iron.ouroborus.net/) is a collection
             of ​Coq formalisations for functional languages of
             increasing complexity. It fills part of the gap between
             the end of the​ Software Foundations course and what
             appears in current research papers.  The collection has
             at least Progress and Preservation theorems for a number
             of variants of STLC and the polymorphic
             lambda-calculus (System F)

*)
(** 先に進む資料としてよいものをいくつか...

       - ソフトウェアの基礎のオプションの章 

       - Cutting-edge conferences on programming languages and formal
         verification:
            - POPL
            - PLDI
            - OOPSLA
            - ICFP
            - CAV
            - (and many others)

       - More on functional programming
            - Learn You a Haskell for Great Good, by Miran
              Lipovaca (ebook)
            - and many other texts on Haskell, OCaml, Scheme, Scala, ...

       - More on Hoare logic and program verification
            - The Formal Semantics of Programming Languages: An
              Introduction, by Glynn Winskel.  MIT Press, 1993.
            - Many practical verification tools, e.g. Microsoft's
              Boogie system, Java Extended Static Checking, etc.

       - More on the foundations of programming languages:
            - Types and Programming Languages, by Benjamin C. Pierce. MIT
              Press, 2002.
            - Practical Foundations for Programming Languages, by Robert
              Harper.  Forthcoming from MIT Press.  Manuscript available
              from his web page.
            - Foundations for Programming Languages, by John C. Mitchell.
              MIT Press, 1996. 
 
       - Coqについて: 
           - Certified Programming with Dependent Types, by Adam
             Chlipala.  A draft textbook on practical proof
             engineering with Coq, available from his web page.
           - Interactive Theorem Proving and Program Development:
             Coq'Art: The Calculus of Inductive Constructions, by Yves
             Bertot and Pierre Casteran.  Springer-Verlag, 2004.
           - Iron Lambda (http://iron.ouroborus.net/) is a collection
             of ​Coq formalisations for functional languages of
             increasing complexity. It fills part of the gap between
             the end of the​ Software Foundations course and what
             appears in current research papers.  The collection has
             at least Progress and Preservation theorems for a number
             of variants of STLC and the polymorphic
             lambda-calculus (System F)

*)

(* $Date: 2014-08-23 15:24:59 -0400 (Sat, 23 Aug 2014) $ *)

