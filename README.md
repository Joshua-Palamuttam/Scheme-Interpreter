# Scheme-Interpreter
This repository contains the work from Joshua Palamuttam, and Ryan Bailey to create an interpreter in scheme for scheme.

All of these Milestone require the chez_init.ss that is included in Milestone 1 and Milestone 2's folder. These milestone's were tested and run using Petite Chez Scheme. Below is some information on what each milestone is, and what features were added to the interpreter. It is important to note that we used a single-file versone of the interpreter so all the code is seperated by comments, which means the parser and unparser are in each of the individual files. 

## Milestone 1
This is a basic interpreter set up

#### Major Features include
- additional primitive procedures (the ones that are needed in order to evaluate the test cases)/n
- literals
- Boolean constants #t, and #f
- quoted values, such as '( ) , '(a b c) , '(a b . (c)) , '#(2 5 4)
- string literals, such as "abc"
- if two-armed only: i.e., (if test-exp then-exp else-exp) You’ll add one-armed if later.
- let (not let* or named let yet; those will appear in later assignments; don't remove them from your parser, though)
- lambda (just the normal lambda with a proper list of arguments) variable-argument lambda gets added later.
- rep and eval-one-exp (two alternative interfaces to your interpreter, described below)
- We suggest that you thoroughly test each feature before adding the next one. Augmenting unparse-exp whenever
you augment parse-exp is a good idea, to help you with debugging. 

## Milestone 2
Expands on the basic interpreter from the previous Milestone

#### Major Features include
- All of the kinds of arguments (proper list, single variable, improper list) to lambda expressions.
- One-armed if: (if <exp> <exp>)
- Whatever additional primitive procedures are needed to handle the test cases I give you. This requirement
applies to subsequent interpreter assignments also.
- syntax-expand allows you (but not necessarily the user of your interpreter) to introduce new syntactic
constructs without changing eval-exp. Write syntax-expand and use it to add some syntactic
extensions (at least add begin, let*, and, or, cond). 
  
## Milestone 3
Just add features for letrec, and named let which contains similar logic

#### Major Features include
- letrec and named let

## Milestone 4
In Milestone 4 there is the complete base interpreter that uses a pass by value, the second is an interpreter which includes 
#### Major Features include
- set! for local (bound) variables
- define (top-level only), including definitions of recursive procedures. You do not need to support the
(define (a b c) e) form or any other forms of define that create procedures without using an explicit lambda.
You do not need to support local defines (i.e. define inside let, lambda or letrec). Your interpreter must support
define inside a top-level begin.
- any additional primitive procedures that are needed for our test cases. More details below.
- set! for global (free) variables. As described in class, you only need to have this work for variables that have already
been defined. More details below.
- reset-global-env
- Procedures with reference parameters
- If top-level-eval or something that it calls creates a global variable or changes the value of a global variable, then the
value of that global variable stays in effect through subsequent calls to eval-one-exp, unless reset-global-env is
called (or unless evaluation of a later expression changes it again).
The purpose of reset-global-env is to handle the case where your interpreter does something wrong and messes up the global
environment when evaluating one of your/my test cases. If we call (reset-global-env), we should then be able to continue
with the rest of the test cases, without your score being adversely affected by the evaluation of the bad (for you) previous test case.
Some of the test cases may call reset-global-env before calling eval-one-exp. Do not fail to implement it.
I suggest that you thoroughly test each additional interpreter feature before adding the next one. It is not required, but updating
unparse whenever you update parse may help you with debugging. 

#### Mini-Assignment for parser
Lexicographically address local variables, and references. This part of the milestone refers to the Interpreter_With_Lexicographical_address.ss file and Interpreter_With_Reference_Parameters.ss

#### In depth analysis of what is done
Modify your parser so it generates lexical-address information for local variable uses and references. Modify apply-env for local
environments so that it uses this lexical address info to efficiently goto the location of a local variable without having to actually compare the
variable to symbols in the environment. This should make the lookup time for a local variable be Θ (lexical depth), since once we get to the
correct local environment, the lookup of the value in the vector will be constant time when we already know the position. The original
apply-env implementation is Θ(number of variables in all local envs). 

## Milestone 5
Transform Milestone 4's base interpreter to Continuation-Passing Style (CPS)

#### Major Features include
- Add display and newline as primitive procedures (and possibly printf) to your interpreted language. 
- Transform Milestone 4's interpreter to Continuation-Passing Style (CPS). 
- Add an exit-list procedure to the interpreted language. It is not quite the same as Chez Scheme's exit; it is
more like (escaper list).
