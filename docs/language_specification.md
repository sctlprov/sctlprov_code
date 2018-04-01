[TOC]

# 1. Introduction
This document specifies the input language of the automated theorem prover SCTLProV. This input language is designed much like a ML-style real world programming language, in order to ease the task of generating Kripke models out of real world computer systems.

# 2. The Input Language
The specification of the new input language is described as follows. In the following des

## 2.1 Lexical tokens
The content of an input file is a sequence of characters, which will be recognized as a sequence of lexical tokens by a lexical analyzer.  

#### Blanks

Blanks is a special kind of lexical tokens and are used to separate other kind of lexical tokens. Blanks are ignored in the parsing of the lexical tokens. The following characters are considered as blanks: space, tabulation, carriage return, and line feed.

#### Comments

The input language supports two styles of comments: C-style and ML-style.

* C-style: `//one-line comment` or `/*multi-line comment*/`
* ML-style: `(*one-line or multi-line comment*)`

Comments are treated as blanks, which are ignored when parsing the input file. The purpose of comments is to make the input file more readable.

#### Identifiers

Identifiers are sequences of ASCII characters. A character in an identifier can be either an English letter, a digit, `_`, or `-`.  There are two kinds of identifiers: identifiers starting with lowercase letters (`ident`), and identifiers starting with a uppercase letter (`uident`):

```
iden	::=   letter {letter|uletter|0...9|_|-}*
uiden	::=   uletter {letter|uletter|0...9|_|-}*
letter	::=   a...z
uletter ::=   A...Z
```

 An `iden` is usually used to denote the name of a value, a type, or a function, etc. An `uiden` is usually used to denote a variant type constructor, or the name of a module.

#### Numeric literals

There are two kinds of numeric literals: integers and floating-points.

```
integer	::= [-]{0...9}+
float	::= [-](0...9)+.{0...9}*
```

#### Keywords

 Keywords are lexical tokens which have special meanings and cannot be treated as identifiers in the input file. The keywords are listed as follows.

```
    Model  Var  Define  Init  Transition  Atomic  Fairness  Spec  int  bool  list
    array  true false   TRUE  FALSE   not  AX  EX  AF  EG  AR  EU   datatype  value
    function  let  match  with  if  then  else ( ) [ ] { } = != < <= > >= + +. - -. 
    * *. / /. ! | || && -> : :: , ; .  
```

## 2.2 Values 

#### Unit

The unit value is written as `()`.

#### Boolean

A Boolean value is either `true` or `false`.

#### Numeric values

 The limit of numbers of values represented for both integers and floating-points are the same as those in OCaml: 

* Integer values are integer numbers from $-2^{30}$ to $2^{30}-1$ on 32-bit platforms, and $-2^{62}$ to $2^{62}-1$ on 64-bit platforms.
* Floating-point values are floating-numbers following the [IEEE 754](https://en.wikipedia.org/wiki/IEEE_754) standard.

#### Scalars

Scalar values are of the form `#iden`, which can be seen as an element of a finite enumeration of symbolic values. For more information about scalars, please read the description of the scalar type.

#### Arrays and Lists

Similar to OCaml, array values are of the form `[|v1 ; ... ; vn[;]|]` and list values are of the form `[v1 ; ... ; vn [;]]`, where  `v1`, ..., `vn` are n values.

#### Tuples

Tuple values are written as `(v1,...,vn)`, where `v1`, ..., `vn` are n values.

#### Records

Records can be seen as labeled tuples of values, which have the form `{l1 = v1 ; ... ; ln = vn [;]}`, where each `li` is a label, and `vi` its corresponding value.

#### Variants

A variant value is either a variant constructor (an `uiden`), or a variant constructor applied to a tuple of values.

```
    value ::= 
          ()
        | true | false
        | integer | float
        | #iden
        | [| value ; ... ; value |] | [ value ; ... ; value ]
        | ( value,...,value )
        | { iden = value ; ... ; iden = value ; }
        | uiden | uiden ( value , ... , value )
```

## 2.3 Expressions and patterns

Expressions are used to build complex values via evluations. The evaluations of expressions in our input language coincide with that of the corresponding OCaml expressions. Values can then be seen as the normal form of expressions, i.e., expressions that cannot be further evaluated.

Patterns are used to match different cases of expressions. The way that patterns match expressions in our input language coincide with that in OCaml.

    expr ::=
          value                                 (*value*)
        | iden                                  (*variable or name of a value*)
        | uiden [(expr,...,expr)]               (*variant expression*)	
        | expr . iden                           (*select one field of a record*)
        | expr [ expr ]                         (*select one field of a array*)
        | ! expr                                (*logical negation*)
        | expr && expr                          (*logical and*)
        | expr || expr                          (*logical or*)
        | - expr                                (*integer negation*)
        | expr + expr                           (*integer addition*)
        | expr - expr                           (*integer subtraction*)
        | expr * expr                           (*integer multiplication*)
        | -. expr                               (*float negation*)
        | expr +. expr                          (*float addition*)
        | expr -. expr                          (*float subtraction*)
        | expr *. expr                          (*float multiplication*)
        | expr = expr                           (*expression equivalence*)
        | expr != expr                          (*expression non-equivalence*)
        | expr < expr                           (*less than*)
        | expr <= expr                          (*less than or equal*)
        | expr > expr                           (*larger than*)
        | expr >= expr                          (*larger than or equal*)
        | ( expr )                              (*expression grouping*)
        | let pattern = expr                    (*declare local variables*)
        | if expr then expr                     (*if-then expression*)
        | if expr then expr else expr           (*if-then-else expression *)
        | expr ; expr                           (*sequence of expressions*)
        | expr <- expr                          (*assignment*)
        | match_expr                            (*pattern matching*)
        | expr with {iden = expr ; ... ; iden = expr [;]}  (*a record with changed bindings*)
        | iden (expr , ..., expr)             (*a function call*)
    
    match_expr ::= match expr with {| pattern -> expr}+
     
    pattern ::= 
          iden 
        | constant
        | pattern :: pattern                    (*list*)
        | ( pattern ,..., pattern )             (*tuple*)
        | _                                     (*match any case*)

## 2.4 Types

Like in read world programming languages, the new input language consists of base types, compound types, and user defined types.

#### Base types

Base types are listed as follows.

1. `unit`: the unit type. `()` the only one constant of type `unit`. Besides, the type of commands is also `unit`.
2. `int`: integer type, whose range depends on the implementation platform of the prover SCTLProV. 
3. `(min .. max)`: integer type within range. Any value `v` of the type `(min .. max)` is an integer value and that `min <= v <= max`.
4. `{#scalar1, #scalar2...,#scalarn}`: scalar type that is used to define an enumeration of finite symbols.
5. `float`: floating-point type, following the IEEE 754 standard.
6. `bool`: boolean type, which consists two dinsguishable values: `true` and `false`.

#### Compound types

* Array 

  An array type is of the form `array t`, where `t` is a type.

* List

  A list type is of the form `list t`, where `t` is a type. 

* Tuple

  A tuple type with n fields is of the form `(t1, t2, ... , tn) `, where `t1`, `t2`, …, `tn` are n data types. An expression of a tuple type with n fields is of the form `(e1, e2, ... ,en)`, where `e1`, `e2`, … , `en` are expressions of types  `t1`, `t2`, …, `tn`, respectively.

* Record

  Records are tuples where each field has an identical name. A record with n fields is of the form `{l1: t1; l2: t2; ... ; ln: tn}`, where `l1`, `l2`, … , `ln` are name of the labels of each field. 

* Variant

  A variant type consists of a finite number of variant constructors separated by the `|` symbol, each of which may be followed by a tuple type.

* Function type

  A function type is used in the declaration of functions, which is described later.


The syntax of `type` is specified as follows.

```
type ::= 
          unit | int | float | bool             (*base types*)
        | (min .. max)                          (*integer type with a range*)
        | {#iden, #iden...,#iden}               (*scalar type*)
        | (type1 , ... , typen)                 (*tuple type*)
        | array type                            (*array type*)
        | list type                             (*list type*)
        | record_type                           (*record type*)
        | variant_type                          (*variant type*)
        | type -> type                          (*function type*)
	   
variant_type ::= constructor | ... | constructor
constructor  ::= uiden | uiden (type , ... , type) 

record_type  ::= { iden : type ; ... ; iden : type ;}
```

## 2.5 Type, value, and function declarations

#### Type declarations

In this language, users can define type aliases by type declarations. Type aliases make the input file more readable. For instance, suppose we want to draw a rectangle in the screen of a monitor, then we need to tell the computer the size of the rectangle, and at what position we want it to draw. In the following code, we defined a rectangle `rect`, and told the computer that the width of `rect` is 10, and the height of `rect` is 20, and the position we want the computer to draw `rect` is (0, 0). 

```
datatype width = int
datatype height = int
datatype x = int
datatype y = int
datatype position = (x, y)
datatype size = (width, height)
value rect : (size, position) = ((10, 20), (0, 0))
```

Moreover, we can also define aliases for more complicated types in the language.  

For instance, in the following code, `object` is a variant type, `Rectangle` and `Circle` are two variant type constructors. Using a variant type, we can define an object that is either a rectangle or a circle in this case. Futhermore, we also want to draw objects that can be filled by colors, for instance, in the following code, if we want the computer to draw a rectangle which is filled by blue color, we can define the drawable value `drawed_rect`, and if we want the computer to draw a circle which is filled by red color, we can define the drawable value `drawed_circle`.

```
datatype width = int
datatype height = int
datatype x = int
datatype y = int
datatype position = (x, y)
datatype size = (width, height)
value rect : (size, position) = ((10, 20), (0, 0))

datatype radius = int
value circle : (radius, position) = (5, (5, 10)) 

//An object can be either a rectangle, or a circle
datatype object = Rectangle (size, position) | Circle (radius, position)
value obj1 : object = Rectangle rect
value obj2 : object = Circle circle

//A expression of type drawable contains two fields: drawing_object and fillcolor
datatype drawable = {
    drawing_object: object;
    fillcolor : {#none, #red, #blue, #yellow};
}
value drawed_rect = {drawing_object = obj1; fillcolor = #blue;}
value drawed_circle = {drawing_object = obj2; fillcolor = #red;}
```

The syntax of type declaractions is as follows.

```
type_decl ::=  datatype iden = type (*to define new types*)
```

#### Value declarations

Value declarations are used to define values on the top level of a program. **Note that values in the language are not global variables.** In contrast to global variables, values are in functional style: when a value is defined, it is bonded by a name, such that neither the binding nor subfields of the value can be changed once defined.

Value declarations are useful to define states in a Kripke model. For instance, in the following code, we define the type of states in a Kripke model to be a pair of integers, and we also define two states: `init` and `bound`.

```
datatype state = (int, int)
value init = (0, 0)
value bound = (10, 10)
```

The syntax of value definition is as follows.

```
value_def ::= value iden = expr		(*value definition*)
```

#### Function declarations

Function declarations in the language are used for the definition of transition relation, atomic formulae, and some other operations to help build transition relation and atomic formulae. 

For instance, in the following code, `next` defines a transition relation: when the current state is `larger` than `bound`, then it goes to itself, otherwise it goes to a new state where both subfields are `increased` by 1. 

```
datatype state = (int, int)
value init = (0, 0)
value bound = (10, 10)

function increase ((fst, snd), x, y) : (state, int, int) -> state =
    (fst + x, snd + y)
function larger ((fst1, snd1), (fst2, snd2)) : (state, state) -> bool = 
	(fst1 > fst2) && (snd1 > snd2)
function next (s) : state -> list state =
	if larger (s, bound) then 
		[s]
	else
		[increase (s, 1, 1)]
```

The syntax of function definition is as follows.

```
fun_decl   ::=  iden ( parameter,...,parameter ) : type = expr
parameter  ::=  iden | ( parameter,...,parameter )
```

**Note: **

**1. (mutually) recursive functions can be defined in the syntax. Thus, programmers should be very careful when defining such kinds of functions, as they may not always terminate. Make sure these functions are applied to a "smaller" data structure each time they are recursivelly called. **

**2. In the function definition, patterns (in the "match … with ..." expression) in a function call may not cover every case of a data structure.  The programmer should also be very careful to make sure every "match … with ..." expression matches every case in the pattern.**

**3. Both the above problems may be avoid in the programming phase by a type system in the future.**

## 2.6 Kripke model declaraction

The definition of Kripke model is the leading role of the input file. All type, value, and function declaractions are used to build a Kripke model in the input file:

- type declaractions are used to define the type of states, or the types of subfields of states;
- value declaractions are used to define the actual states, or the values of subfields of states;
- function declaractions are used to define the transition relation and atomic formulae, and also their helper operations.

**In order to make sure that the Kripke model defined is valid, values are functinal, i.e., subfields of values cannot be changed once defined. Although programmers can define local variables in a function body whose bindings of values may change in the function body, their value are functional once returned. This is to make sure that when doing an operation (e.g., a step of transition) on a state, the value of this state would not change.**

The Kripke model is specified by the declaration as follows.

```
kripke_decl ::=  
    Model { 
       (*Define states as lists of state variable bindings (a record), this is optional.*)
       Vars { iden : type ; ... ; iden : type ; }

       (*Define the initial state (refered to as either "ini" or "init"), also optional.*)
       Init { iden := expr ; ... ; iden := expr ; }

       (*Define the transition relation.*)
       Transition { next iden := transitions }

       (*Define atomic formulae.*)
       Atomic { {iden ( iden , ... , iden ) := expr ;}* }		

       (*Define fairness constraints, optional.*)
       Fairness { formula ; ... ; formula }

       (*Define the specification.*)
       Spec { iden := formula ; ... ; iden := formula ;}
    }

trasitions ::= 
      expr 
    | expr : expr ; ... ; expr : expr ;
			
formula ::= 
         iden ( iden , ... , iden )
       | not formula
       | formula /\ formula
       | formula \/ formula
       | EX ( iden , formula , expr )
       | AX ( iden , formula , expr )
       | EG ( iden , formula , expr )
       | AF ( iden , formula , expr )
       | EU ( iden , iden , formula , formula , expr )
       | AR ( iden , iden , formula , formula , expr )
```

## 2.7 Program Structure

Programs are organized as modules. Each modules contains a set of declarations. Modules can be imported into others, while cyclic dependencies are not allowed. 

```
module ::= 
    import uiden ... import uiden
    decl ... decl
decl   ::= type_decl | value_decl | fun_decl

main_file ::= kripke_decl | module kripke_decl
```

