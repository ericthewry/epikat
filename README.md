# Epik -- Epistemic <span style="font-variant:small-caps;">Kat</span>

Epik is a modelling tool for representing the intensional semantics of natural
language sentences. Users specify valid world states, events that transition
between states, epistemic agents, and the inferences the agents make from the
worlds. Together these represent a space of possible worlds in which the user
can evaluate the logical forms of sentences. More information can be found in
our SCiL '21 paper.

> # TODO link paper once it has a stable link.

_The Concealed Coin_ If there are two agents at a table `Amy` and `Bob` who are
curious about whether a concealed coin is heads-up or tails-up (lets say its
been flipped and covered with a sheet of paper befor either party could look at
the coin).

To represent this situation, we first need to write down the possible states of
the coin (heads-up or tails-up), which are just boolean variables.

 ```
 state heads tails
 ```
 
It would be feasible to model a coin with a single variable `heads`, and encode
`tails` as `~heads`, but using two separate variables means that we need to
restrict certain bogus states (thereby demonstrating how to use the restriction
facility). We want to eliminate situations like `heads & tails`, and `~heads &
~tails`, both of which are physically impossible (assuming the coin is
infinitessimally thin and there's a breeze).

To prevent theses bogus situations we use the `restrict` operator to describe
the valid world-states:
```
restrict (heads + tails) & ~(heads&tails)
```
This formula says that one of `heads`/`tails` is true, and not both of them are.

Now we can describe the events that can take place in the world.

 

