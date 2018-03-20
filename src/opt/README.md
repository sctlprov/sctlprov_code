# 1 Introduction

This is the implementation of the SCTL system, named SCTLProV. The source code of SCTLProV is written in programming language OCaml. Some important files in this project are listed as follows.

- term.ml: definition of expressions, states, and relative functions.
- formula.ml: definition of formulae, and relative functions.
- modul.ml: definition of modules, and relative functions.
- prover.ml: implementation of rewrite rules over continuation-passing trees, and relative functions.
- prover_bdd.ml: another prover module where BDDs are used to store sets of states.
- prover_output.ml: another prover module that can produce more output.
- bdd.ml: simple interfaces of using BDDs in this project.
- main.ml: entry of the whole project.
- lexer.mll: lexer generator.
- parser.mly: parser generator.
- river.model: an illustrative example.
- LICENSE: the license file.
- README.md: this file.

# 2 How to Compile the Source Code

1. Install [OCaml](https://ocaml.org/), [opam](https://opam.ocaml.org/), and install [mlcuddidl](https://opam.ocaml.org/packages/mlcuddidl/) via opam;
2. Input `make win` (`make linux`) in the windows command line (linux terminal) , or input `make win-opt` (or `make linux-opt` in the linux terminal) if you want a optimized version. 
3. If option 2 failed, then just copy the corresponding commands in the file `Makefile` and compile the code by hand.
4. If your installization fails anyway, try to update OCaml into the latest version (4.04.0 for now), and then compile the source code following the above steps.


# 3 How to Use The Tool

General Usage:

	sctl [-bdd] [-output <output_file_name>] input_file_name

- Use BDDs to store sets of states, if option `-bdd` is specified.
- Output the proof tree to file `output_file_name` if option `-output output_file_name` is specified.


**In practice, SCTLProV runs faster (not very much) when the `-output` option is not specified. 
So if efficiency is your main concern, do not use the output option.
When option `-bdd` is specified, SCTLProV usually consumes more time and less memory space than not using `-bdd` option.**


# 4 An illustrative example

This example concerns the so-called River Crossing Puzzle
problem.  The question is how can the farmer bring the wolf, the goat,
and the cabbage get across the river?  We formalize this problem as a
Kripke model `M` and the question as a specification.  The initial
state `ini` of model `M` has four components: the initial
position of the farmer, the wolf, the goat, and the cabbage.  Every
transition from one state to another corresponds to every move of the
farmer from one side of the river to another, whether he will carry
the wolf, the goat, or the cabbage or not.  The specification is that
if there exists a state `s` can be reachable from `ini`, such
that in `s`, all of them get on the other side of the river.  the
farmer, the wolf, the goat, and the cabbage have crossed the river.
These data compose the input file (`river.model`) as listed below:

	Model River_Crossing()
	{
		Var 
		{
			farmer:Bool; wolf:Bool; goat:Bool; cabbage:Bool;
		}
	 	Init 
		{
			farmer:=false; wolf:=false; goat:=false; cabbage:=false;
		}
		Transition
		{ 
			farmer=wolf:    {wolf:=!wolf;};
		   	farmer=goat:    {goat:=!goat;};
		   	farmer=cabbage: {cabbage:=!cabbage;};
		   	true:           {farmer:=!farmer;};
		}	
		Atomic
		{
			safe(s):=!(s(wolf)=s(goat)&&s(wolf)!=s(farmer))&&!(s(goat)=s(cabbage)&&s(goat)!= s(farmer));
		 	complete(s):=s(farmer)=true&&s(wolf)=true && s(goat)=true&&s(cabbage)=true;
		}
		Spec
		{ 
			find:=EU(x,y,safe(x),complete(y),ini);
		}
	}


Note that in this input file, two atomic formulae: `safe(s)` and
`complete(s)` are given.  `safe(s)` being true means that, in state
`s`, neither the goat nor the cabbage can be eaten; `complete(s)`
being true means that, in state `s`, the farmer, the wolf, the goat,
and the cabbage all of them have crossed the river. The identifier
`ini` represents the initial state. 

For checking the specification, we can use the
following command:

	sctl -output output.out river.model

and the result will display as below: 

	verifying on the model River_Crossing...
	find: EU(x,y,safe(x),complete(y),ini)
	find is true, proof output to "output.out".

# 5 Benchmarks

The benchmarks are avaliable in [this website](https://github.com/terminatorlxj/ctl_benchmarks). 

# 6 Visualization

We also wrote an visualization tool for the visualization of proof trees, called VMDV, which is also avaliable in [this website](https://github.com/terminatorlxj/vmdv). The proof tree produced by SCTLProV can be visualized in 3D space by VMDV. Interested readers may refer to the README file of VMDV for further usage information.

# 7 Syntax of input files
The purpose of the SCTL specification language is to describe a finite state model and the specification to be verified against the model. To define a finite model, one usually needs to define the notion of state, the initial state, and the transitions relation between states. We design our language to be suited to describe these three parts of a finite state model. In addition, in the SCTL system, a notion of atomic formulae is introduced to represent either property of a single state or relations between multiple states. We also can specify this in our language. As for the specification of the finite state model, we use the SCTL formulae, instead of CTL formulae, by extending CTL with polyadic predicate symbols.


## 7.1 Lexical Tokens
The content of an input file is an sequence of characters, which will be recognized as a sequence of lexical tokens by the lexical analyzer. Among these tokens, a number is a sequence of digits, an identifier is a sequence of characters beginning with an alphabetic character, and followed by any sequence of characters in the set `{A-Z, a-Z, 0-9, _}`.

The keywords are listed below:

		Module Model  Var  Define Init Transition Atomic Spec Int Bool 
		true   false  TRUE FALSE  not  AX  EX  AF   EG   AR   EU

Any other tokens are in quotes in the syntax descriptions.


## 7.2 Expressions
Expressions in the language consist of variables, constants, and a collections of operator-connected expressions. The syntax of expressions is as follows.

	expr ::
	        iden                ;;variable or symbol
	      | iden "(" expr ")"   ;;expression evaluated at a state
	      | iden "." iden       ;;local variable of a module
	      | number              ;;integer constant
	      | "true"              ;;logical constant true
	      | "false"             ;;logical constant false
	      | "#" iden            ;;scalar constant
	      | "!" expr            ;;logical negation
	      | expr "&&" expr      ;;logical and
	      | expr "||" expr      ;;logical or
	      | "-" expr            ;;integer negation
	      | expr "+" expr       ;;integer addition
	      | expr "-" expr       ;;integer subtraction
	      | expr "*" expr       ;;integer multiplication
	      | expr "=" expr       ;;expression equivalence
	      | expr "!=" expr      ;;expression non-equivalence
	      | expr "<" expr       ;;less than
	      | expr "<=" expr      ;;less than or equal
	      | expr ">" expr       ;;larger than
	      | expr ">=" expr      ;;larger than or equal

Expressions match the pattern `iden "(" expr ")"` only appear in the definition of atomic formulae, which means the expression inside the parentheses are evaluated only at a specified state. This will be explained later in the atomic formulae definition section. The order of precedence of the operators from low to high is

	||
	&&
	+, -
	*
	=, !=, <, <=, >, >=
	!

Operators of equal precedence are associate to the left. One can also use parentheses to group expressions.


## 7.3 State Variables Declaration
A state in the finite state model is an assignment of a set of state variables. The state variable declaration begins with a `Var` keyword, and between `"{"` and `"}"` appears the definition of each variable along with its type. The type of a state variable can be either a Boolean, a subrange of the integer set, a scalar, or a user defined module.

	var_decl :: "Var" 
	            "{"
	              iden ":" type ";"
	              iden ":" type ";"
	              ...
	            "}"

and

	type ::
	        Bool                                ;;boolean type
	      | "(" expr ".." expr ")"              ;;subrange type
	      | "{" "#"iden "," "#"iden "," ..."}"  ;;scalar type
	      | iden                                ;;user defined module



## 7.4 User Defined Symbols
It is often more concise if using one single symbol to represent complicated or commonly used expressions. The declarations of symbols begins with a `Define` keyword and are surrounded by `"{"` and `"}"`.

	symbol_decl :: "Define" 
	               "{"
	                 iden ":=" expr ";"
	                 iden ":=" expr ";"
	                 ...
	               "}"

Note that symbols can be used anywhere an expression is expected to appear. The declaration of user defined symbols is optional in the input file.


## 7.5 Initial State Declaration
The initial assignment of the state variables formed the initial state of the finite state model. The declaration of the initial assignments for all state variables begins with a `Init` keyword and are surrounded by `"{"` and `"}"`.

	init_decl :: "Init"
	             "{"
	               iden ":=" expr ";"
	               ...
	               iden ":=" iden "(" expr "," expr "," ... ")"
	               ...
	             "}"

Note there are two kinds of assignments for the state variables: the assignment of a state variable by an expression, and the assignment of a state variable by an instance of a user defined module. For instance, when the assignment `"p := m(1, true)"` appears in the initial state declaration of module `m'`, this means that the state variable `p` in module `m'` is initially assigned by the initial assignment of the state variables in the module `m`, instantiated by the given parameter `1` and `true`. Suppose `x` is a state variable for module `m`, then one can get the assignment of `x` in module `m'` by referring to `p.x`.


## 7.6 Transition Relation Declaration
The transition relation defines the transitions from one state to another. The declaration of transition relation begins with a `Transition` keyword, and are surrounded by `"{"` and `"}"`.

	trans_decl :: "Transition"
				  "{"
					 expr ":" "{" iden ":=" expr ";" iden ":=" expr ";" ... "}" ";"
					 ...
				  "}"

The transition relation is defined by a set of transition options, where each transition option is formed by an guarded expression and a set of state variable assignments. For instance, the transition option `"v1=v2 : {v3 := v5+v6; v7 := v8;}` means that when we compute the next state `s'` of state `s`, we first evaluate the guarded expression `v1=v2` at state `s`, and if it evaluates to a truth value, then we assign the value of `v5+v6` to `v3`, and the value of `v8` to `v7` in state `s'`. Both `v5+v6` and `v8` are evaluated at state `s`. There maybe more than one transition options defined in the transition declaration, and if more than one guarded expressions are evaluated to true, then it refers to a non-deterministic transition.


## 7.7 Atomic Formulae Declaration
By extending CTL with polyadic predicates, SCTL enables us not only to express properties of one single state, but also relations between more than one states in an atomic formula.

	atomic_decl :: "Atomic"
	               "{"
	                 iden "(" iden "," iden "," ... ")" ":=" expr ";"
	                 ...
	               "}"

For instance, `"atom1(s1, s2) := (s1(v1) = s2(v2))"` defines an atomic formula `atom1(s1, s2)` such that this formula is true if and only if the assignment of the state variable `v1` at state `s1` equals to the assignment of the state variable `v2` at state `s2`.

## 7.8 Fairness Constraints Declaration
The fairness constraints are characterized by a list of SCTL formulae.

	fairness_decl :: "Fairness"
					 "{"
						formula ";"
						formula ";"
						...
					 "}"
and

	formula ::
		     "TRUE"                                ;;Top
		   | "FALSE"                               ;;Bottom
		   | iden "(" iden "," iden "," ... ")"    ;;atomic formula
		   | "not" formula
		   | formula "/\" formula
		   | formula "\/" formula
		   | "AX" "(" iden "," formula "," iden ")"
		   | "EX" "(" iden "," formula "," iden ")"
		   | "AF" "(" iden "," formula "," iden ")"
		   | "EG" "(" iden "," formula "," iden ")"
		   | "AR" "(" iden "," iden "," formula "," formula "," iden ")"
		   | "EU" "(" iden "," iden "," formula "," formula "," iden ")"
		   | "(" formula ")"


## 7.8 Specification Declaration

	spec_decl :: "Spec"
	             "{"
	               iden ":=" formula ";"
	               ...
	             "}"


## 7.9 Module Declaration
There are two kinds of module declarations in the language: modules containing the declaration of atomic formulae and specification, called the main modules; and modules do not contain the declaration of atomic formulae and specification, called sub-modules. There is exactly one main modules and may be more than one sub-modules in an input file. The main module is like the main function to an C file, while the sub-modules are like normal C functions. The declaration of a main module starts with a `Model` keyword, and the declaration of a sub-module starts with a `Module` keyword.

	main_module_decl :: 
	   "Model" iden "(" [iden ":" type ","] ... ")"
	   "{"
	      var_decl
	      [symbol_decl]
	      init_decl
	      trans_decl
	      atomic_decl
		  [fairness_decl]
	      spec_decl
	   "}"

and 

	sub_module_decl :: 
	  "Module" iden "(" [iden ":" type ","] ... ")"
	  "{"
	     var_decl
	     [symbol_decl]
	     init_decl
	     trans_decl
	  "}"


## 7.10 Program Structure
A program is formed by a set of declarations of modules.

	program ::
	          [sub_module_decl]
	          ...
	          main_module_decl

The declaration of sub-modules is optional in an input file.

(end)


