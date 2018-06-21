
#  Syntax of input language for the finite version
The purpose of the SCTL specification language is to describe a finite state model and the specification to be verified against the model. To define a finite model, one usually needs to define the notion of state, the initial state, and the transitions relation between states. We design our language to be suited to describe these three parts of a finite state model. In addition, in the SCTL system, a notion of atomic formulae is introduced to represent either property of a single state or relations between multiple states. We also can specify this in our language. As for the specification of the finite state model, we use the SCTL formulae, instead of CTL formulae, by extending CTL with polyadic predicate symbols.


## 1 Lexical Tokens
The content of an input file is an sequence of characters, which will be recognized as a sequence of lexical tokens by the lexical analyzer. Among these tokens, a number is a sequence of digits, an identifier is a sequence of characters beginning with an alphabetic character, and followed by any sequence of characters in the set `{A-Z, a-Z, 0-9, _}`.

The keywords are listed below:

		Module Model  Var  Define Init Transition Atomic Spec Int Bool 
		true   false  TRUE FALSE  not  AX  EX  AF   EG   AR   EU

Any other tokens are in quotes in the syntax descriptions.


## 2 Expressions
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


## 3 State Variables Declaration
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



## 4 User Defined Symbols
It is often more concise if using one single symbol to represent complicated or commonly used expressions. The declarations of symbols begins with a `Define` keyword and are surrounded by `"{"` and `"}"`.

	symbol_decl :: "Define" 
	               "{"
	                 iden ":=" expr ";"
	                 iden ":=" expr ";"
	                 ...
	               "}"

Note that symbols can be used anywhere an expression is expected to appear. The declaration of user defined symbols is optional in the input file.


## 5 Initial State Declaration
The initial assignment of the state variables formed the initial state of the finite state model. The declaration of the initial assignments for all state variables begins with a `Init` keyword and are surrounded by `"{"` and `"}"`.

	init_decl :: "Init"
	             "{"
	               iden ":=" expr ";"
	               ...
	               iden ":=" iden "(" expr "," expr "," ... ")"
	               ...
	             "}"

Note there are two kinds of assignments for the state variables: the assignment of a state variable by an expression, and the assignment of a state variable by an instance of a user defined module. For instance, when the assignment `"p := m(1, true)"` appears in the initial state declaration of module `m'`, this means that the state variable `p` in module `m'` is initially assigned by the initial assignment of the state variables in the module `m`, instantiated by the given parameter `1` and `true`. Suppose `x` is a state variable for module `m`, then one can get the assignment of `x` in module `m'` by referring to `p.x`.


## 6 Transition Relation Declaration
The transition relation defines the transitions from one state to another. The declaration of transition relation begins with a `Transition` keyword, and are surrounded by `"{"` and `"}"`.

	trans_decl :: "Transition"
				  "{"
					 expr ":" "{" iden ":=" expr ";" iden ":=" expr ";" ... "}" ";"
					 ...
				  "}"

The transition relation is defined by a set of transition options, where each transition option is formed by an guarded expression and a set of state variable assignments. For instance, the transition option `"v1=v2 : {v3 := v5+v6; v7 := v8;}` means that when we compute the next state `s'` of state `s`, we first evaluate the guarded expression `v1=v2` at state `s`, and if it evaluates to a truth value, then we assign the value of `v5+v6` to `v3`, and the value of `v8` to `v7` in state `s'`. Both `v5+v6` and `v8` are evaluated at state `s`. There maybe more than one transition options defined in the transition declaration, and if more than one guarded expressions are evaluated to true, then it refers to a non-deterministic transition.


## 7 Atomic Formulae Declaration
By extending CTL with polyadic predicates, SCTL enables us not only to express properties of one single state, but also relations between more than one states in an atomic formula.

	atomic_decl :: "Atomic"
	               "{"
	                 iden "(" iden "," iden "," ... ")" ":=" expr ";"
	                 ...
	               "}"

For instance, `"atom1(s1, s2) := (s1(v1) = s2(v2))"` defines an atomic formula `atom1(s1, s2)` such that this formula is true if and only if the assignment of the state variable `v1` at state `s1` equals to the assignment of the state variable `v2` at state `s2`.

## 8 Fairness Constraints Declaration
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


## 8 Specification Declaration

	spec_decl :: "Spec"
	             "{"
	               iden ":=" formula ";"
	               ...
	             "}"


## 9 Module Declaration
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


## 10 Program Structure
A program is formed by a set of declarations of modules.

	program ::
	          [sub_module_decl]
	          ...
	          main_module_decl

The declaration of sub-modules is optional in an input file.

(end)


