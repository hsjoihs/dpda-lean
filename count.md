# Counting the number of PPP-DPDA

The number of possible transition functions for a predetermined-to-push-or-pop DPDA (PPP-DPDA) is relatively small.

## When lumping the "pushing"-state and the "popping"-state together

Let $|Q| = q, |\Gamma| = \gamma, |\Sigma| = \sigma$. 

Then 
$$|Q \cup(\Sigma \nrightarrow Q)| = q + |\Sigma \rightarrow (Q \cup \lbrace\text{undefined}\rbrace)| = q + (1+q)^\sigma$$

$$|\Gamma_Z \nrightarrow (Q \cup (\Sigma \nrightarrow Q))| = \Bigl(1+q + (1+q)^\sigma\Bigr)^{\gamma+1}$$

Since the type of the transition function is 

$$\dot{\delta} : Q \rightarrow \Bigl[ (\Gamma \times Q) \cup (\Gamma_Z \nrightarrow (Q \cup (\Sigma \nrightarrow Q))) \Bigr]$$

we have the total count

$$N(q, \gamma, \sigma) = \Biggl[\gamma q + \Bigl(1+q + (1+q)^\sigma\Bigr)^{\gamma+1}\Biggr]^{q}$$

For instance, if we restrict ourselves to parsing a binary alphabet using a single stack symbol, then $\gamma = 1, \sigma = 2$, and the number of possible transition functions is $\Biggl[ q + \Bigl(1+q + (1+q)^2\Bigr)^{2}\Biggr]^{q} \sim q^{4q}$.

| $q$ | $N(q, 1, 2)$ |
|-----|--------------:|
| 1   | 37           |
| 2   | 21316        |
| 3   | 65450827     |
| 4   | 6.678e+11    |
| 5   | 1.732e+16    |
| 6   | 9.621e+20    |

## When separating the "pushing"-state and the "popping"-state

Let $x,y$ be the number of states for the "pushing"-state and the "popping"-state, respectively.  

Then

$$\dot{\delta} :\Bigl( X \rightarrow  (\Gamma \times Q),Y \rightarrow  (\Gamma_Z \nrightarrow (Q \cup (\Sigma \nrightarrow Q)))  \Bigr)$$

gives the total count of

$$N(x, y, \gamma, \sigma) = \Bigl(\gamma (x+y)\Bigr)^{x} \Bigl(1+x+y + (1+x+y)^\sigma\Bigr)^{(\gamma+1)y}$$

