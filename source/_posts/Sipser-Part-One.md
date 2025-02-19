---
title: Sipser Part One
toc: true
date: 2023-04-11 16:10:43
tags:
categories:
mathjax: true
---


# Introduction to the Theory of Computation  Michael Sipser

with MIT 18.404 Theory of Computation
[2020 Fall PPT](https://math.mit.edu/~sipser/18404/Lectures%20Fall%202020/index.html)

## Part One: Automata and Languages

### Lecture 1

#### Automata, computability and complexity


Finite Automaton
1. a model of computer with limited capacity
2. state diagram of finite automaton

<!--more-->

- states, transitions, start state, accept states
- Input: finite string; Output: Accept or Reject
  - The language of the machine: collection of strings that can be accepted by the machine
   - A is the language of M <=> M recognize A <=> A = L(M)
- A Math Def: A finite automaton M is a 5-tuple (Q,$\mathrm{\Sigma}$,$\delta$,$q_0$,F).
  - Q: finite set of states.
  - $\mathrm{\Sigma}$: finite set of alphabet symbols.
  - $\delta$: transition function  $\delta:Q\times\mathrm{\Sigma}\rightarrow Q$
   - F: set of accepted state
   - Languages and Expressions
   - 	A **string** is a finite sequence of symbols in $\mathrm{\Sigma}$  (the empty string, the string of length 0).
   - A **language** is a set of strings (finite or infinite)  (the empty language, the set with no strings).
  - a regular language means that it can be applied to a finite automaton
     - e.g.: B = { w | w has an even number of 1s}  is regular; while C = {w | w has equal numbers of 0s and 1s} is not regular
- Regular Expressions
   - Union: $A\cup B={w|w \in A \in or\ w\in B}$
   - Concatenation: $A\circ B={xy | x \in A\ and \ y \in B}=AB$
   - Star: $A^\ast={x_1\ldots x_k|each\ x_i \in A \ fork \geq 0}$ (we always have $\epsilon \in A^\ast$)
   - **Theorem**: (Closure under union operation) If $A_1, A_2$ are regular languages, so is $A_1\cup A_2$
     - **Proof**: Given $M_1 \rightarrow A_1$,$M_2 \rightarrow A_2$, construct $M$ that accept $w$ of $M_1$ or $M_2$ accepts $w$
      - Components of $M$:
        - $Q=Q_1\times Q_2= \{ \left( q_1,q_2 \right) |q_1\in Q_1 and q_2\in Q_2 \} $
        - $q_0= \left( q_1,q_2 \right)$
        - $\delta\left(\left(q,r\right),a\right)=\left(\delta_1\left(q,a\right),\delta_2\left(r,a\right)\right)$
        - $F=\left(F_1\times Q_2\right)\cup\left(Q_1\times F_2\right)$

- Nondeterministic Finite Automata
  - Features:
    - To a given status and a given transition, there might me more than one way to go or having no way to go.
    - allow $\epsilon$-transition (“free” movement without reading input)
    - Accept input if some path lead to accept status (Acceptance overrules rejections)
  - Definition:
    - The definition of a NFA is similar to DFA except   $\delta:Q\times\mathrm{\Sigma}_\epsilon\rightarrow P\left(Q\right)=R|R\subseteq Q$
  - Ways to think about nondeterminism:
    - Computational: Fork new parallel thread and accept if any thread leads to an accept state
    - Mathematical: Tree with branches. Accept if any branch leads to an accept state
    - Magical: Machine always makes the right guess that leads to accepting, if possible.
  - **Theorem**: If an NFA recognizes A, then A is regular
    - **Proof**: Let NFA $M=\left(Q,\mathrm{\Sigma},\delta,q_0,F\right)$ recognize A, construct DFA $M^\prime=\left(Q^\prime,\mathrm{\Sigma},\delta^\prime,q_0^\prime,F^\prime\right)$ recognizing A
  - **Theorem**: If A is a regular language, so is $A^\ast$
  - **Theorem**: If R is a regular expo and A = L(R) then A is regular



### Lecture 3

1. Finite automata $\rightarrow$ regular expressions.
2. Proving languages are't regular.
3. Context free grammars

- DFAs $\rightarrow$ Regular Expressions
  - We have just explored conversion R $\rightarrow$ NFA M $\rightarrow$ DFA M’
  - **Theorem**: If A is regular, then A = L(R) for some regular expo R
  - **Proof**: Give conversion DFA M $\rightarrow$ R

- Generalized NFA
  - **Def**: A Generalized Nondeterministic Finite Automaton (GNFA) is similar to an NFA, but allows regular expressions as transition labels
    - may read a whole string in one step
    - Assume that: 
      - Only have one accept state, which is separate from the start state (All previous accept state point to a new accept state)
      - One arrow from each state to each other state, except that we can only exiting the start state and can only entering the accept state (use empty language regular expression)
    - **Lemma**: Every GNFA has an equivalent regular expression R

<!--  
![](/img/sipser_lec3_pic1.png)
-->

  - **Lemma**: Every GNFA has an equivalent regular expression R
    - **Proof**: By induction on the number of states k of G
    - Basis: k=2, let R = r.
    - Induction step (k>2): Assume Lemma true for k-1 states and prove for k states, then convert k state GNFA to equivalent k-1 state GNFA.
    - So we can convert GNFAs to regular expressions, and similarly we can also convert DFAs to regular expressions.
  - How  can we prove that a language is not regular?
    - **Pumping Lemma**: For every regular language A, there is a p such that if $s \in A$ and $\left| s \right| \geq p$ then $s=xyz$ where
      - $xy^iz \in A$ for all $i \geq 0 y^i=yy...y$
      - $y \neq \epsilon$
      - $\left| xy \right| \leq p$
    - Variant: Combine closure properties with the pumping lemma.
      - Find a contradictory example (which might be denoted by intersection of several languages, this can prove that all the languages are not regular).
      - Chomsky normal form:
        - A context-free grammar is in Chomsky normal form if every rule is of the form: $A \rightarrow BC$, $A \rightarrow a$  where $a$ is any terminal and $A$,$B$ and $C$ are any variables — except that $B$ and $C$ may not be the start variable. In addition, we permit the rule $S \rightarrow \epsilon$, where $S$ is the start variable.
        - Any context-free language is generated by a context-free grammar in Chomsky normal form.

### Lecture 4: Pushdown Automata, CFG <-> PDA

- **Context Free Grammars**
  - **Rule**: Variable -> string of variables and terminals
  - **Variables**: Symbols appearing on left-hand side of rule
  - **Terminals**:  Symbols appearing only on right-hand side
  - **Start Variable**: Top left symbol
  - **Productions**: A grammar consists of a collection of substitution rules
  - e.g. G1:   S -> 0S1;  S -> R;   R -> $\epsilon$;
    - in G1, there are 3 rules, 2 variables (R,S), 2 terminals (0,1), and 1 start variable (S)
    - Use or (|) symbol to write shorthand rules
  - **Grammars generate strings**: 
    - Write down start variable.
    - Replace any variable according to a rule. Repeat until only terminals remain.
    - Result is the generated string.
    - L(G) is the language of all generated strings.
    - We call L(G) a Context Free Language.
  - **Formal Definition**:
    - A Context Free Grammar G is a 4-tuple $(V,\mathrm{\Sigma},R,S)$
    - $V$: finite set of variables
    - $\Sigma$: finite set of terminal symbols
    - $R$: finite set of rules
    - $S$: start variable
      - for $u,v \in (V \cup \mathrm{\Sigma})^\ast$ write
        - $u \rightarrow v$ if can go from u to v with one substitution step in G
        - $u \overset{*}{\rightarrow} v$ if can go from u to v with some number of substitution steps in G, and the whole sequence is called a derivation of v from u
    - A is a Context Free Language if A=L(G) for some CFG G
      - If a string has two different parse trees then it is derived ambiguously and we say that the grammar is **ambiguous**
  - Schematic diagram: a higher level description for pushdown automata
    - Schematic diagram for DFA or NFA:
      - input appears on a “tape” (or we call it an “input tape”), the tape have a “head”
      - and we have a finite control unit
    - Schematic diagram for PDA
      - there is going to be a (pushdown) stack
      - PDA might use its stack as a kind of unbounded memory, allow fir operations like write-add (push) or read-remove (pop) symbols from the top of the stack
        - e.g. the we can construct PDA for $D= \{ 0^k 1^k | k \geq 0 \} $
          - Read 0s from input, push onto stack until read 1
          - Read 1s from input, while popping 0s from stack
          - Enter accept state of stack is empty. Note: acceptance only at end of input.
      - Formal definition of pushdown automaton
        - A **Pushdown Atomaton** is a 6-tuple $(Q,\mathrm{\Sigma},\mathrm{\Gamma},\delta,q_0,F)$
        - $\Sigma$: input alphabet.
        - $\Gamma$: stack alphabet.
        - $\delta:Q \times \mathrm{\Sigma}_\epsilon \times \mathrm{\Gamma}_\epsilon \rightarrow P \left( Q \times \mathrm{\Gamma}_\epsilon \right) \delta \left( q,a,c \right) = \left( r_1, d \right) , \left( r_2, e \right) $, use state and symbols to denote the transition movement.
      - Converting CFGs to PDAs
        - Theorem: If A is a CFL iff some PDA recognize A
        - "->" can be proved with relative ease.
        - "<-" would be harder
      - Corollaries
        - Every regular language is a CFL
        - If A is a CFL and B is regular, then A $\cap$ B is a CFL.
- Recursive
  - We might divide the process: $A_{pq} \rightarrow A_{pr} A_{rq}$, $ \left( A_{pp} \rightarrow \epsilon, A_{pq} \rightarrow a A_{rs} b \right)$ (where a is the input read at the first move, b is the input read at the last move, r is the state following p, and s is the state preceding q).



### Lecture 5: CF Pumping Lemma, Turing Machine
  1. Proving languages not context free
  2. Turing Machines
  3. T-recognizable and T-decidable languages
- Pumping Lemma for CFLs
  - For every CFL A, there is a p such that if $s\in A$ and $\left| s \right| \geq p$ then $s=uvxyz$ where  
    1. $u v^i x y^i z \in A$ for all $i \geq 0$
    2. $vy \neq \epsilon$
    3. $\left| vxy \right| \le p$
  - Informal definition: All long strings in A are pumpable and stay in A.
- The class of CFls is closed under intersection, concatenation and kleen star, but not closed under union.
- Deterministic Context-Free Languages (DCFLs): subset to non-deterministic context-free languages
  - DCFLs include $0^n1^n$ but do not include $ww^R$.
  - **Lemma**: Every DPDA has an equivalent DPDA that always reads the entire input string.
    - To tackle with the problem of hanging and looping, use symbol \$ as the bottom of the stack. If detected midway, reject; if not detected by the end of input, reject; if detected at previous accept state, accept.
  - **Theorem**: The class of DCFLs is closed under complementation.
  - Reject
    - hanging: when the machine tries to pop an empty stack, initialize the stack with a special symbol to identify this reject situation.
    - looping: when the machine makes an endless sequence of $\epsilon$.




