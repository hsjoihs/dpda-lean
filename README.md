# Proving the equivalence of various DPDA formulations in Lean
Formulating DPDAs (deterministic push-down automata) following the principles of "make invalid states unrepresentable"

## Abstract

This repository serves as the formal proof of the LaTeX summary available here: https://www.overleaf.com/project/65b4903d4d2168e01882cbfa

[A TypeScript version](https://github.com/hsjoihs/various-DPDA-formulations-ts) is also available.

## Conventions

The standard way in the literature is to incorporate $Z_0$ into $\Gamma$ and **trust** that the designer of the DPDA would always put back a $Z_0$ at the bottom whenever it is consumed. Here I seek to make a formulation that does not rely on such trust. Hence, I will assume that the an stack returns $\text{undefined}$ when popped. 

For the purpose of readability, I let $\Gamma_Z = \Gamma \cup \lbrace \text{undefined} \rbrace$ in which $\Gamma_Z$ is understood to be always the result of popping from a stack.

I use $U \nrightarrow V$ and $U \rightarrow (V \cup \lbrace\text{undefined}\rbrace)$ interchangeably.


I will use the concept of "wobbly functions" that I have introduced in the LaTeX summary. A wobbly function is a function that may or may not consume its input. 

In mathematical notation, let $U \stackrel{{\sqcup}}{\nrightarrow} V$ to mean $(U \nrightarrow V) \cup V$ for sets $U$ and $V$.  

## Five equivalent formulations of DPDA

Here, I will present five different formulations of deterministic pushdown automata (DPDA) that are proven (in the LaTeX summary) to be equivalent in power. I name the five formulations as follows:

1. Predetermined-to-push-or-pop DPDA: [./Dpda/PredeterminedToPushOrPop.lean](./Dpda/PredeterminedToPushOrPop.lean)
2. Push-or-pop DPDA #1
3. Push-or-pop DPDA #2: [./Dpda/PushOrPop2.lean](./Dpda/PushOrPop2.lean)
4. (≤1, ≤1)-DPDA: [./Dpda/Le1PopLe1Push.lean](./Dpda/Dpda/Le1PopLe1Push.lean)
5. Character-popping, string-pushing DPDA (a.k.a. (1, n)-DPDA): [./Dpda/CharPopStringPush.lean](./Dpda/CharPopStringPush.lean)

Each model allows for a different way of defining the transition function, while all adhering to the principle of "make invalid states unrepresentable" and, most importantly, makes every transition deterministic.

The following table shows which stack operations are allowed under each formulation:

| Formulation | No-op<br> (ε ⇒ ε) | Push1<br> (ε ⇒ B) | Pop1<br> (A ⇒ ε) | Replace(1,1)<br> (A ⇒ B)  | Replace(1,n)<br> (A ⇒ BCDE)  | 
| --- | --- | --- | --- | --- | --- |
| Predetermined-to-push-or-pop DPDA | No | Yes | Yes | No | No |
| Push-or-pop DPDA #1, #2 | No | Yes | Yes | No | No |
| (≤1, ≤1)-DPDA | Yes | Yes | Yes | Yes | No |
| (1,n)-DPDA | Yes*<sup>[1]</sup> | Yes*<sup>[1]</sup> | Yes | Yes | Yes |

[1]: attainable by implementing a "no-op (ε ⇒ ε)" or a "push1 (ε ⇒ B)" as a "pop and then push back" operation (that is, A ⇒ A and A ⇒ B)


## The type of transition functions under each formulation

The transition function encodes the behavior of the DPDA. The key difference in the five formulations lies in the way the transition function is defined. Hence, I will first provide the types of the transition functions for each of the five formulations.

`interconversion.ts` contains functions that convert between the five formulations. The TypeScript compiler will check that the converters makes sense in terms of types (i.e. whether the definitions typechecks), but it will not check that the converters are actually semantically correct.  
The conversions 1 → 2, 2 → 3, 3 → 4, and 4 → 5 are basically an increasingly intricate inclusion maps. The conversion 5 → 1 is quite non-trivial and in general increases the number of states.

### 1. Predetermined-to-push-or-pop DPDA (PPP-DPDA)

#### Mathematical representation

$$\dot{\delta} : Q \rightarrow \Bigl[ (\Gamma \times Q) \cup (\Gamma_Z \nrightarrow (Q \cup (\Sigma \nrightarrow Q))) \Bigr]$$

or, equivalently,

$$\dot{\delta} : Q \rightarrow \Bigl[ (\Gamma \times Q) \cup (\Gamma_Z \nrightarrow  (\Sigma \stackrel{{\sqcup}}{\nrightarrow} Q)) \Bigr]$$

#### Explanation

In this deterministic pushdown automaton (DPDA), the designer must predetermine (at every state $q$) whether to push or pop a symbol from the stack.

The left branch, $(\Gamma \times Q)$, represents the case where the DPDA unconditionally pushes a symbol onto the stack. The right branch, $(\Gamma_Z \nrightarrow (Q \cup (\Sigma \nrightarrow Q)))$, represents the case where the DPDA first pops a symbol from the stack and then decides whether to consume the input or not.

In terms of doing exhaustive analysis (i.e. generating all the possible DPDAs and analyzing them), I argue that this is one of the best formulations that makes invalid states unrepresentable. 

The advantage of this formulation is that it is very concise and finite. For instance, if $|Q| = 3, |\Gamma| = 1, |\Sigma| = 2$, then the number of possible transition functions is $403^3 = 65450827$. [See the count.md file for more details.](count.md)

The downside to this conciseness and finiteness is that it is quite tedious and painful to program in.  
For instance, a typical DPDA might want to do the following:

- At $q_0$, if the input is $a$, push $A$ onto the stack and stay on $q_0$.
- At $q_0$, if the input is $b$, pop $A$ from the stack and move to $q_1$.

Since the choice of whether to push or pop is predetermined in this formulation, we can't write this "push $A$" as an "unconditional push", forcing us to use "pop and then decide whether to consume". Thus we need to split "push $A$" into "pop $A$" + "push $A$" + "push $A$". Hence this predetermined-to-push-or-pop DPDA is very impractical and non-intuitive to use.


### 2. Push-or-pop DPDA #1

Mathematical representation:

$$ \ddot{\delta} : Q \rightarrow \Biggl[ (\Gamma \times Q)\cup \Bigl(\Sigma \nrightarrow ( (\Gamma \times Q)\cup( \Gamma_Z \nrightarrow \lbrace\varepsilon\rbrace \times Q))\Bigr)\ \cup\  \Bigl(\Gamma_Z \nrightarrow (\Sigma \stackrel{{\sqcup}}{\nrightarrow} Q)\Bigr)\ \Biggr]$$

### 3. Push-or-pop DPDA #2

Mathematical representation:

$$ \ddot{\delta} : Q \rightarrow \Biggl[ \Bigl(\Sigma \stackrel{{\sqcup}}{\nrightarrow} ( (\Gamma \times Q)\cup( \Gamma_Z \nrightarrow \lbrace\varepsilon\rbrace \times Q))\Bigr)\ \cup\  \Bigl(\Gamma_Z \nrightarrow (\Sigma \stackrel{{\sqcup}}{\nrightarrow} \lbrace\varepsilon\rbrace \times Q)\Bigr)\ \Biggr]$$

### 4. (≤1, ≤1)-DPDA
#### Mathematical representation

$$ \hat{\delta} : Q \rightarrow \Biggl[ \Bigl(\Sigma \stackrel{{\sqcup}}{\nrightarrow} (\Gamma_Z \stackrel{{\sqcup}}{\nrightarrow} \Gamma_\varepsilon \times Q)\Bigr)\ \cup\  \Bigl(\Gamma_Z \nrightarrow (\Sigma \stackrel{{\sqcup}}{\nrightarrow} \Gamma_\varepsilon \times Q)\Bigr)\ \Biggr] $$ 

where $\Gamma_\varepsilon := \lbrace j \in \Gamma^* \mid \text{len}(j) \le 1 \rbrace \cong \Gamma \cup \lbrace \varepsilon \rbrace $.

#### Explanation


(≤1, ≤1)-DPDA is inspired by the formulation given in Sipser<sup>[2]</sup>, which however only focuses on non-deterministic pushdown automata.

[2]: Michael Sipser. *Introduction to the Theory of Computation*. Course Technology, Boston, MA, third edition, 2013.

### 5. Character-popping, string-pushing DPDA

Mathematical representation:

$$ \tilde{\delta} : (Q \times \Gamma_Z)  \to \Bigl[ (\Sigma \nrightarrow \Gamma^* \times Q ) \ \cup \ (\Gamma^* \times Q )\  \cup \lbrace \text{undefined} \rbrace \Bigr] $$

or, equivalently,

$$ \tilde{\delta} : (Q \times \Gamma_Z) \to \Bigl[ (\Sigma \stackrel{{\sqcup}}{\nrightarrow}  \Gamma^* \times Q ) \  \cup \lbrace \text{undefined} \rbrace \Bigr] $$
