[TOC]

# 1. Introduction
This document specifies the input language of the automated theorem prover [SCTLProV](https://github.com/terminatorlxj/SCTLProV). This input language is designed much like a ML-style real world programming language, in order to ease the task of generating Kripke models out of real world computer systems.

# 2. The Input Language
The specification of the new input language is organized to 4 parts: 

1. Lexical tokens;
2. Datatype declarations;
3. Expression and function declarations;
4. Comments;
5. Programe structures.  

## 2.1 Lexical tokens
The content of an input file is a sequence of characters, which will be recognized as a sequence of lexical tokens by a lexical analyzer. Among these tokens, a number is a sequence of digits, an identifier is a sequence of characters beginning with an alphabetic character, and followed by any sequence of characters in the set `{A-Z, a-Z, 0-9, _}`.

The keywords are listed below:

```
	Model  Var  Define Init Transition Atomic Fairness Spec int bool list array
	true  false  TRUE FALSE  not  AX  EX  AF  EG  AR  EU datatype value function 
	let match with if then else 
```

Any other tokens are in quotes in the syntax descriptions.

## 2.2 Datatype declarations
Like in read world programming languages, the new input language consists of base types, compound types, and user defined types.

### 2.2.1 Base types

Base types are listed as follows.

1. `unit`: the unit type. `()` the only one constant of type `unit`. Besides, the type of commands is also `unit`.
2. `int`: integer type, whose range depends on the implementation platform of the prover SCTLProV. For instance, if SCTLProV is implemented in 32-bit OCaml platform, then the range of the type `int` is [-2^31^, 2^31^-1].
3. `(min .. max)`: integer type within range. Any value `v` of the type `(min .. max)` is an integer value and that `min <= v <= max`.
4. `{#scalar1, #scalar2...,#scalarn}`: scalar type that is used to define an enumeration of finite symbols.
5. `float`: double precision (64 bits) floating-point type, following the IEEE 754 standard.
6. `bool`: boolean type, which consists two dinsguishable values: `true` and `false`.

### 2.2.2 Compound types

* Tuple

  A tuple type with n fields is of the form `(t1, t2, ... , tn) `, where `t1`, `t2`, …, `tn` are n data types. An expression of a tuple type with n fields is of the form `(e1, e2, ... ,en)`, where `e1`, `e2`, … , `en` are expressions of types  `t1`, `t2`, …, `tn`, respectively.

* Record

  Records are tuples where each field has an identical name. A record with n fields is of the form `{l1: t1; l2: t2; ... ; ln: tn}`, where `l1`, `l2`, … , `ln` are name of the labels of each field. 

* Array 

  An array type is of the form `array t`, where `t` is a type.

* List

  A list type is of the form `list t`, where `t` is a type. 


### 2.2.2 User defined types

In addition to base types and compound types, the language provides a machanism to define new types.

In this language, users can define type aliases. For instance, suppose we want to draw a rectangle in the screen of a monitor, then we need to tell the computer the size of the rectangle, and at what position we want it to draw. In the following code, we defined a rectangle `rect`, and told the computer that the width of `rect` is 10, and the height of `rect` is 20, and the position we want the computer to draw `rect` is (0, 0). 

```
datatype width = int
datatype height = int
datatype x = int
datatype y = int
datatype position = (x, y)
datatype size = (width, height)
value rect : (size, position) = ((10, 20), (0, 0))
```
In addition to type aliases, users can also define new types via type constructors. There are two kinds of type constructors supported in the language: variants and records. 

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

Type asiases, variant types, and record types are called user defined types in the language. The definition of user defined data types is the major way to define new data types. 

The syntax of user defined types is as follows.

```
udt_def ::=   "datatype" iden "=" udt (*to define new types*)
udt ::= variant_type | record_type | type

variant_type ::= constructor {"|" constructor}*
constructor ::= Iden | Iden type 

record_type ::= "{" {type_bingding}* "}"
type_binding ::= iden ":" type ";"
```

**Remark:**  An `Iden` is an `iden` with the first letter in upper case.

The syntax of `type` is specified as follows.

```
type ::= 
	     unit | int | float | bool 		(*base types*)
	   | (type, type, ... , type)								(*tuple type*)
	   | array type												(*array type*)
	   | list type												(*list type*)
	   | udt													(*user defined type*)
	   | type "->" type											(*function type*)
```

## 2.3 Expressions

Expressions are terms of given types. 

```
expr ::=
        iden                (*variable or constructor name*)
      | expr "." iden		  (*select one field of a record*)
      | expr "[" expr "]"	  (*select one field of a array*)
      | "!" expr            (*logical negation*)
      | expr "&&" expr      (*logical and*)
      | expr "||" expr      (*logical or*)
      | "-" expr            (*integer negation*)
      | expr "+" expr       (*integer addition*)
      | expr "-" expr       (*integer subtraction*)
      | expr "*" expr       (*integer multiplication*)
      | "-." expr 			   (*float negation*)
      | expr "+." expr		(*float addition*)
      | expr "-." expr 		(*float subtraction*)
      | expr "*." expr 	   (*float multiplication*)
      | expr "=" expr       (*expression equivalence*)
      | expr "!=" expr      (*expression non-equivalence*)
      | expr "<" expr       (*less than*)
      | expr "<=" expr      (*less than or equal*)
      | expr ">" expr       (*larger than*)
      | expr ">=" expr      (*larger than or equal*)
      | "(" expr ")"		(*expression grouping*)
      | "let" pattern "=" expr					(*declare local variables*)
      | "if" expr "then" expr [ "else" expr ] 	(*if expression*)
      | expr ";" expr							(*expression with effect*)
      | expr "<-" expr							(*assignment*)
      | match_expr								(*pattern matching*)
      | expr "with" "{" {iden "=" expr ";"}* iden "=" expr [";"] "}"
      						(*a record with changed bindings*)
      

constant ::= ()
		   | number
		   | "[]"
		   | "[||]"
		   | "true"
		   | "false"
      
match_expr ::= "match" expr "with" {"|" pattern "->" expr}+

pattern ::= iden 
		  | constant
		  | pattern "::" pattern			(*list*)
		  | "(" {pattern ","}+ pattern ")" 	(*tuple*)
		  | "_"								(*match any case*)
```

Expressions can be used to define constants, variables, and functions in a program.

### 2.3.1 Values

The value definition is used to define values on the top level of a program. **Note that values in the language are not global variables.** In contrast to global variables, values are in functional style: when a value is defined, it is bonded by a name, such that neither the binding nor subfields of the value can be changed once defined.

Value definitions are useful to define states in a Kripke model. For instance, in the following code, we define the type of states in a Kripke model to be a pair of integers, and we also define two states: `init` and `bound`.

```
datatype state = (int, int)
value init = (0, 0)
value bound = (10, 10)
```

The syntax of value definition is as follows.

```
value_def ::= "value" iden "=" expr		(*value definition*)
```

### 2.3.2 Functions

Function definitions in the language are used for the definition of transition relation, atomic formulae, and some other operations to help build transition relation and atomic formulae. 

For instance, in the following code, `next` defines a transition relation: when the current state is `larger` than `bound`, then it goes to itself, otherwise it goes to a new state where both subfields are `increase`d by 1. 

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
fun_def ::= iden "(" args ")" "=" expr
args ::= pattern [":" type] {"," pattern [":" type]}*
```

**Note: **

**1. (mutually) recursive functions can be defined in the syntax. Thus, programmers should be very careful when defining such kinds of functions, as they may not always terminate. Make sure these functions are recursivelly called on a "smaller" data structure each time. **

**2. In the function definition, patterns (in the "match … with ..." expression) in a function call may not cover every case of a data structure.  The programmer should also be very careful to make sure every "match … with ..." expression matches every case in the pattern.**

**3. Both the above problems may be avoid in the programming phase by a type system in the future.**

## 2.4 Comments
Comments in the input file are of the following forms.
```
//a one-line comment
/*a multi-line comment*/
(*a one-line or multi-line comment*)
```

## 2.5 Kripke model

The definition of Kripke model is the leading role of the input file. All datatype definitions, value definitions, and function definitions are used to build a Kripke model in the input file:

- datatype definitions are used to define the type of states, or the types of subfields of states;
- value definitions are used to define the actual states, or the values of subfields of states;
- function definitions are used to define the transition relation and atomic formulae, and also their helper operations.

**In order to make sure that the Kripke model defined is valid, values are functinal, i.e., subfields of values cannot be changed once defined. Although programmers can define local variables in a function body whose bindings of values may change in the function body, there value are functional once returned. This is to make sure that when doing an operation (e.g., a step of transition) on a state, the value of this state would not change.**

The Kripke model is specified by the declaration as follows.

```
kripke_def ::= "Model" "{"
				/*
                Define states as lists of state variables (a record),
                this is optional.
              */
				[
					"Vars"  "{" 
						{iden ":" type ";"}+ 
					"}" 
				]
				/*
				Define the initial states (refered to as either "ini" or "init"), 
				also optional.
				*/
				[
                  	"Init" "{"
                  		{iden ":=" expr ";"}+
                  	"}"
				]
				//Define the transition relation
				"Transition" "{"
					"next" iden ":=" {expr ":" expr ";"}+
 				"}"
 				//Define atomic formulae
				"Atomic" "{"
					{iden "(" {iden ","}* iden ")" ":=" expr ";"}*
				"}"
				//Define fairness constraints
				"Fairness" "{"
					{formula ";"}* formula
				"}"
				//Define the specification
				"Spec" "{"
					{iden ":=" formula ";"}+
				"}"
			"}"
			
formula ::= iden "(" iden {"," iden}* ")"
		  | "not" formula
		  | formula "/\" formula
		  | formula "\/" formula
		  | "EX" "(" iden "," formula "," expr ")"
		  | "AX" "(" iden "," formula "," expr ")"
		  | "EG" "(" iden "," formula "," expr ")"
		  | "AF" "(" iden "," formula "," expr ")"
		  | "EU" "(" iden "," iden "," formula "," formula "," expr ")"
		  | "AR" "(" iden "," iden "," formula "," formula "," expr ")"
```

## 2.5 Program Structure

Programs are organized as modules. Each modules contains a set of declarations. Modules can be imported into others, while cyclic dependencies are not allowed.

```
kripke_model ::= 
		{"import" iden}*
		{udt_def | value_def | fun_def}*
		[kripke_def]
```

