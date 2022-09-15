## Overall Structure

``
theory {{module_name}}
  imports {{imported files, including xxx in `from xxx imports yyy`}}
begin

{{contract declarations & structure declarations & enum}}

{{monad definitions for each functions, methods, modifiers}}

locale semantic_{{module_name}} = solidity_project +
  {{public methods list}}
begin
{{specifications of each functions, methods, modifiers}}
end

end
```

module\_name ≡ source-file-name without extension, replacing space by underscore.
  It must be composition of alphabet, number and underscore, greek letter, prime only.
  Tell me if some special characters are not in this set, we may represent it by some greek letter or special encoding.

Note, for every function, method, and modifier, you need to translate them by twice, in two different forms, Monadic and Isar. Later in detail we give the specification.

## Structural Declarations

### Contract Declarations

```
decl_contract {{name}}
decl_contract {{name}} < {{parents, separated by comma, at least one}}
```

### Structural Declaration

```
decl_sem_type {{name}} =
  {{field_name}} : \<open>{{type}}\<close>
  ...
```

#### Encoding of types

| Integer for n bits | \<tau>Int n   |
|--------------------|---------------|
| Boolean            | \<tau>Int 1   |
| Address            | \<tau>Address |
| Reference to data on ledge* | \<tau>LedgeRef |
| Structure          | \<tau>Ref     |

*: including mapping, ledge-array.

### Enum

```
decl_enum {{name}} =
  {{value}}
  ...
```

### Public Method List

TBD

## Monadic Representation of Functions etc

Every definition of a function, modifier, method will be translated into a definitoin in monad representation.
In this section, we first introduce briefly what is monadic representation and then how to translate a function definition.

### Introduction of monadic representation

An instruction and any composition of instruction, and so any fragment of a function, is represented by a Monad.

A monad, can be a lambda expression, like `(λx. body)`. A lambda expression resembles a unary function, where, the lambda variable `x` is the argument of the function, and `body` is an expression about `x`, e.g. `(λx. x + 1)`.

Note, in a lambda expression, `f x` means call a lambda function f by value x. `f (g x)` means, first call g by x and then call f by the result of `g x`. All lambda functions are unary. `f x y` means, first call f by x, and it returns another function, and then call this function by y. Here `f` is a function that returns another function, like `f = λx. (λy. x + y)`, and we have `f 1 = (λy. 1 + y)` and `f 1 2 = 1 + 2`.

Two monad `f,g`, can be composed, `f \<bind> g` (or `f >>= g` as you seen the previous day), which means first execute f and pass the result of f to g to execute g.

Because Monads are all unary, we need a way to encode / aggregate arguments. (Actually there are two encodings, one for the ordinary and another using lists for the case when the arity is unknown. Here we only give the ordinary encoding and we give the other until it is used).

- for nullary `f`, call it by `f \<phi>V_none` or `f` directly.
- for unary `f`, call by `f x`
- for N-ary `f`, call by `f (\<phi>V_pair x1 (\<phi>V_pair x2 (\<phi>V_pair x3 x4)) ....)`

Note the return of a monad is also unary, we need a way to encode multi-return and to extract every element from it.

Take an example, `f \<bind> (λtwo_ret. g (first_of two_ret) \<bind> f (second_of two_ret))`.

We use `\<phi>V_fst` for the first_of above. `\<phi>V_fst` extract the first element of a return list. A bit of unnature for non-functional programming user, we use `\<phi>V_snd` to extract the remaining list of returns filtering out the first. It may be clearer by giving definition, `\<phi>V_fst (a,b) ≡ a` and `\<phi>V_snd (a,b) ≡ b`. For a list of more than 2 elements, we represent it recursively like, `x = (1,(2,(3,(4,5))))`. So that, to get the 3rd element in this case, we use `\<phi>V_fst (\<phi>V_snd (\<phi>V_snd x))`, becasue, `\<phi>V_snd x = (2,(3,(4,5)))` and `\<phi>V_snd (\<phi>V_snd x) = (3,(4,5))`.

That is, `\<phi>V_fst ret` is always the first element of ret if ret has at least more than 1 elements; `\<phi>V_snd ret` is the second element of ret is ret has exactly 2 elements, but if ret has more than 2 elements, the second element is `\<phi>V_fst (\<phi>V_snd ret)`.

#### An Example

Expression `X + Y` will be translated to
```
X \<bind> (\<lambda> x. Y \<bind> (\<lambda y. op_int_add 32 (\<phi>V_pair x y)))
```

Note it is illegal to be `op_int_add 32 (\<phi>V_pair X Y)` because `X, Y` here are programs that can only be connected by `\<bind>`. They are not values even if they are expressions!

#### Convention

Always translate into right-associative form, e.g. `X \<bind> (\<lambda> x. Y \<bind> (\<lambda> y. Z))` instead of left-associative form like `(X \<bind> Y) \<bind> Z`, though they can be equivalent.

#### Annotations / Parameters

Monad can be parameterized by type annotations. Like `op_int_add 32 (\<phi>V_pair x y)`, here 32 is a parameter of op_int_add annotating it is a 32-bit operation. Note 32 is not an operand of th e instruction, the operand is `(\<phi>V_pair x y)`, so here we do not encode it by `\<phi>V_pair`.

Form of monads:
```
<monad>  <parameters>  <argument list by \<phi>V_pair>
```

#### Higher Order Parameter

Some monad accecpts other monads as its parameters. Those parameters are called higher order parameters. For example, the opcode `if` has 0 arguments but 3 higher order parameters for expression of condition, body of true branch, and body of false branch respectively.

```
op_if (condition) (true-branch) (false-branch)
```

As an example, `if (1 < x) then x - 1 else x` can be
```
op_if (get_var "x" \<bind> (\<lambda> x. op_const 1 \<bind> (\<lambda> y. op_less (\<phi>V_pair x y))))
  (get_var "x" \<bind> (\<lambda> x. op_const 1 \<bind> (\<lambda> y. op_sub (\<phi>V_pair x y))))
  (get_var "x")
```

We use higher order parameter to represent control flow.


### Translating a Functional Definition

#### Function

```
definition \<open>{{func_name}} \<equiv> {{its monadic representation}} \<close>
```

Then we talk the monadic representation of a function.

**Arguments** are represented by **a** lambda variable using the encoding of `\<phi>V_fst` and `\<phi>V_snd` given above. `(\<lambda>arg. body)`

Note, any solidity function translated by you should always have an argument even if it is nullary. Translate it to this, ``(\<lambda>(_::unit sem_value). {{body}})``. Anytime when you call this function, call it by `\<phi>V_none`. However, most of nullary opcode does not have an argument. Call them directly without an argument, like, `opcode` instead of `opcode \<phi>V_none`.

#### Modifier

A modifier is a higher-order monad that accepts the monadic representation of a function and returns the monad of the modified function.
```
definition \<open>{{modifier_name}} \<phi>underscore \<equiv> {{its monadic representation}} \<close>
```
All occurrences of the underscore in its body are replaced by `\<phi>underscore`.
Explain: above `\<phi>underscore` is a higher-order parameter representing the function to modify.

Note, though a modifier itself doesn't have argument, since the function it 

**Application of a modifier in a function**, is just call the modifier by giving the function body as its parameter `\<phi>underscore`. That is, like,
```
definition \<open>{{func_name}} \<equiv> {{modifier_1}} ({{modifier_2}} ({{its monadic representation}})) \<close>
```

**Note**, for a **virtual** modifier, you must by using analysis tools built in solidity compiler, find out which exact modifier a function refers to, and translate it to that exact modifier. The reasoning framework built on Isabelle does not parse / analysis which modifier it exactly refers to.


### Mapping of Each Opcode to its Monad

TBD

## Isar representation of functions and modifiers

### Overview

For each function, the template looks like,
```
proc {{name}}:
  argument \<open>\<cdots>\<close>
  return \<open>\<cdots>\<close>
  throws \<open>\<cdots>\<close>
  apply (rule modifier_{{modifier_1}})
  ...
  apply (rule modifier_{{modifier_n}})
  \<medium_left_bracket>
    {{body}}
  \<medium_right_bracket>
```

For modifiers, it will be,
```
proc {{name}}:
  assumes \<phi>underscore: \<open>\<bold>p\<bold>r\<bold>o\<bold>c \<phi>underscore \<lbrace> X \<longmapsto> Y \<bold>t\<bold>h\<bold>r\<bold>o\<bold>w\<bold>s E \<rbrace>\<close>
  argument \<open>\<cdots>\<close>
  return \<open>\<cdots>\<close>
  throws \<open>\<cdots>\<close>
  \<medium_left_bracket>
    {{body}}
  \<medium_right_bracket>
```


## Scratch

PragmaDirective -> version "XXX"

ImportDirective -> import xxxx
  note: unfold all x in `import "abc" as x`, `import * as x from "abc"`, `import {a as b, c} from "abc"`

theory Name
  imports ...


Literal -> to natural number, 
