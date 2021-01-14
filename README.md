# Epik -- Epistemic <span style="font-variant:small-caps;">Kat</span>

Epik is a modelling tool for representing the intensional semantics of natural
language sentences. Users specify valid world states, events that transition
between states, epistemic agents, and the inferences the agents make from the
worlds. Together these represent a space of possible worlds in which the user
can evaluate the logical forms of sentences. More information can be found in
our SCiL '21 paper.

> # TODO link paper once it has a stable link.

## Tutorial : The Concealed Coin
As a running example to showcase the features of Epik, we will re-use the
concealed coin example from the paper. If there are two agents at a table `Amy`
and `Bob` who are curious about whether a concealed coin is heads-up or tails-up
(lets say its been flipped and covered with a sheet of paper befor either party
could look at the coin).

### Declaring State Variables

To represent the concealed coin states, we first need to write down the possible states of
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

### Restricting to Valid World States
To prevent theses bogus situations we use the `restrict` operator to describe
the valid world-states:
```
restrict (heads + tails) & ~(heads&tails)
```
This formula says that one of `heads`/`tails` is true, and not both of them are.

### Declaring Events

Now we can describe the events that can take place in the world, for example we
can have an event where `Amy` peeks at  a heads-up coin, which we can write as

``` 
event amy_peeks_heads (test heads):(test heads)
```

This declaration both declares the event `amy_peeks_heads` and defines its pre-
and post-condions, namely that the coin must be heads-up both before and after
the event. We can declare events `amy_peeks_tails`, `bob_peeks_tails` and
`bob_peeks_heads` similarly.

```
event amy_peeks_tails (test tails):(test tails)
event bob_peeks_heads (test heads):(test_heads)
event bob_peeks_tails (test tails):(test_heads)
```

We can also write down events that can happen in multiple states, namely the
event `nop`, which doesn't change the state, but can happen when it's either
heads or tails.

```
event nop (test heads):(test heads) + (test tails):(test tails)
```

This event says that either the coin starts heads up and stays heads up, or it
starts tails and stays tails, i.e. it doesn't change whether the coin is heads-up or
tails-up.

We can encode state changes in our events, such as the event in which `Amy`
secretly turns the coin over from one state to the other, with no knowledge from
`Bob`. We can encode this as two events.

``` 
event amy_turns_heads (test heads):(test tails)
event amy_turns_tails (test tails):(test heads)
```

And similarly for `Bob``:
``` 
event amy_turns_heads (test heads):(test tails)
event amy_turns_tails (test tails):(test heads)
```

### Epistemic Alternatives

The final piece of the model to define is epistemic alternatives for the agents,
these are the events that each agent can "infer" from an event in the "base
world". For example, `Amy`'s alternatives for the event `bob_peeks_heads` are
`bob_peeks_heads + bob_peeks_tails`, because she does not know whether he peeked
at `heads` or at `tails`, only that he peeked at something. `Amy` has the same
alternatives for `bob_peeks_tails`, and Bob has analogous alternative for
`amy_peek_heads` and `amy_peek_tails`. Conversely, `Amy` knows exactly what she
saw for each of her `peek`, events so the alternative relation on those events is the identiy.

To define `Amy`'s' epistemic relation , simply write `agent amy` followed by a
new alternative relation on each line. For instance, the rows for the `peek`
events are as follows,`Bob`'s relation is analogous. 
 

```
agent amy 
  ... other events ...
  (amy_peeks_tails -> amy_peeks_tails)
  (amy_peeks_heads -> amy_peeks_heads)
  (bob_peeks_heads -> bob_peeks_heads + bob_peeks_tails)
  (bob_peeks_tails -> bob_peeks_heads + bob_peeks_tails)
  ... other events ...
```

For both `Amy`'s and `Bob`'s event relations on all of the aforementioned events
see [demo.k](testkf/demo.k).

> N.B. This example is identical to the one described in Figure 2 in the paper
> modulo the name changes. For a the same model as in the paper see
> [figure2.k](testkf/figure2.k).

### Evaluating Queries

Then we can write queries using the syntax

``` 
query <name> = <query>
```

For example, the worlds where `Bob` learns that `Amy` peeked at heads because he
also peeked at heads can be written as:

```
query bob_ever_peeks_heads = _*;bob_peeks_heads;_*
query amy_ever_peeks_heads = _*;amy_peeks_heads;_*
query bob_believes_amy_peeked_heads = 
  amy_ever_peeks_heads & 
  ~bob(~(bob_ever_peeks_heads&amy_ever_peeks_heads))
```

Here the operator `bob(k)` represents taking the preimage of `bob`'s alternative
relation on worlds, `~` represents negation, `;` is sequencing, `_` represents
any action, `&` is the intersection of worlds, and `k*` is one or more
occurences of term `k`.

#### Beliefs

We can also represent mistaken beliefs. For instance, if `Bob` doesn't see that
`Amy` turns the coin over, and then he peeks at heads he may believes that she
peeked at heads, when actually she peeked at tails.

```
query bob_is_wrong =
  amy_peeks_tails;amy_turns_tails;bob_peeks_heads 
  & ~bob(~(amy_peeks_heads;_;_))
```

Here `&` indicates an intersection of sets of worlds, and `_` indicates an arbitrary world. 

#### Knowledge

We can also compute the 3-event worlds in which `Bob` _knows_ that Amy peeked at heads,
as in, he believes that she peeked at heads, and she truly did.

```
query bob_is_correct =
  amy_ever_peeks_heads & ~bob(~(amy_ever_peeks_heads))
```

This notion of "justified true belief" is a bit wonky, because the justification
comes from the event alternative, which might be misleading. Really this only
captures "true beliefs", and can only be said to be true knowledge if the
alternative relation is in a certain form. See the paper for details.

## Building and Installing Epik from Source

Install `git` and clone this respository. Change into the toplevel directory,
probably it will be named `epik`, unless you manually specified a different
name.

### Prerequisites

Install the prerequisite software. First you will need `stack`, which is a build
system for Haskell Softaware. Install it using your package manager, e.g. on
Ubuntu run `[sudo] apt install haskell-stack`.

Now use stack to install the project dependencies:

```
stack install happy
stack install alex
```

If `stack` complains about any other missing packages, install those too.

To build the project, run `stack build --copy-bins`.

## Running Epik

Now you can run `epik` as a command line tool. There are two outputs, lists of
guarded strings, and `fst` code.

### Computing lists of guarded strings

For example, to compute the guarded strings that correspond to the above
queries, simply run `epik gs 8 testkf/demo.k`. This may take a few moments. The
second parameter `8` tells `epik` to compute no more than `8` guarded strings
per query. If you would like to see more detail you can increase this as large
as you would like.

### Generating fst code  

To generate `fst` code, you can run `epik fst testkf/demo.k` and then run
`xfst`, to interact with the generated model

## Other resources

> TODO Mats

# Issues

If you run into issues, please use Github's built-in issue tracker, or reach out
to the authors at the email addresses specifed in the SCiL 2021 paper.
