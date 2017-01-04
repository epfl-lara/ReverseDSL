# ReverseDSL

The problem is to reverse a function's behavior.
Reversing a function `F` means that we compute `F'` such that if we have:

    F(I) = O

where `I` is the initial input and `O` is the initial output,
then

    F'(I, O') = I' such that
    F(I') = O'

and `I'` is as close as possible to `I`, where "closest" can be measured in terms of a generalized [Levenshtein distance](https://en.wikipedia.org/wiki/Levenshtein_distance).
Ideally, we would like that the distance betten `I` and `I'` is no more than the distance between `O and O'`

## Functions reversed so far.
We demonstrate the technology of reversing a function on the following examples.
Note that the inversion might return several feasible inputs, we only display the first for readability.
You can run the tests using

    sbt test

### String concat

    Original inputs: ("Hello", " ", "world")
    => output = "Hello world"
    If output = "Hello Buddy",     inputs = ("Hello",  " ", "Buddy")
    If output = "Hello big world", inputs = ("Hello",  " ", "big world")
    If output = "Hello underworld",inputs = ("Hello",  " ", "underworld")
    If output = "Hellooo world",   inputs = ("Hellooo"," ", "world")
    If output = "Hello  world",    inputs = ("Hello",  "  ","world")
    If output = "Hi world",        inputs = ("Hi",     " ", "world")

### Int sum

    Original inputs: (2, 3, 1)
    => output = 6
    If output = 5, outputs = (2,3,0)
    If output = 4, outputs = (2,3,-1)
    If output = 7, outputs = (2,3,2)
    
#### with Z3 and variables
This is not working yet:

    Original inputs: {val a = 1; (a, 3, a) }
    => output = 5
    If output = 4, inputs = (a, 2, a) //'
    If output = 3, inputs = (a-1, 3, a-1) //'
    If output = 6, inputs = (a, 4, a) //'
    If output = 7, inputs = (a+1, 3, a+1) //'*/

### List partition
The partition function separates the list into (odds, evens).
Inserion of an even number where there weren't any.

    Original inputs: List(3, 5)
    => output = (List(3, 5), List())
    If output = (List(3, 5), List(4)),  inputs = List(4, 3, 5)       (2 more)

Removal of an even number in the output

    Original inputs: List(3, 4, 5)
    => output = (List(3, 5), List(4))
    If output = (List(3, 5), List()),   inputs = List(3, 5)

Inserion of an even number in the output.

    Original inputs: List(1, 2, 3, 4, 5)
    => output = (List(1, 3, 5), List(2, 4))
    If output = (List(1, 3, 5), List(2, 6, 4)),   inputs = List(1, 2, 6, 3, 4, 5)     (1 more)

### Typed split

Written in the DSL of [WebBuilder](https://github.com/epfl-lara/leon/blob/master/library/leon/webDSL/webBuilding/WebBuilder.scala), the following examples

    Original inputs: List(^.width := "100px", <.pre, ^.height := "100px", ^.src := "http")
    => output = (List(<.pre), List(^.src := "http"), List(^.width := "100px", ^.height := "100px"))
    If output = (List(<.pre), List(^.src := "http"), List(^.width := "100px", ^.outline := "bold", ^.height := "100px")),
            inputs = List(^.width := "100px", <.pre, ^.outline := "bold, ^.height := "100px", ^.src := "http")
    If output = (List(<.pre), List(^.src := "http"), List(^.width := "100px"))
            inputs = List(^.width := "100px", <.pre, ^.src := "http")

### Composition

Reversing composition of functions is possbile if each has its inverses provided.
For example, given:

    val f = (x: Int) => x - (x % 2)
    val g = (x: Int) => x - (x % 3)

    val fRev = (x: Int) => if(x % 2 == 0) List(x, x+1) else Nil
    val gRev = (x: Int) => if(x % 3 == 0) List(x, x+1, x+2) else Nil

we can define the reverse of the composition `f andThen g` as:

    composeRev(f, g) = (x: Int) => gRev(x).flatMap(fRev)

For the above functions, the following tests work:

    composeRev(f, g)(0) = List(0, 1, 2, 3)
    composeRev(f, g)(3) = List(4, 5)
    composeRev(f, g)(6) = List(6, 7, 8, 9)

### Flatten
Flattening a list can also be reversed using the initial input as an hint.
We un-flatten by closing lists as fast as possible, except when the added element is the last, in which case we append it to the last list.

    Original input = List(List(1, 2, 3), List(5, 6), List(), List(7))
    => output = List(1, 2, 3, 5, 6, 7)
    If output = List(1, 2, 5, 6, 7), then
             input = List(List(1, 2), List(5, 6), List(), List(7))
    If output = List(1, 2, 3, 4, 5, 6, 7), then
             input = List(List(1, 2, 3), List(4, 5, 6), List(), List(7))
    If output = List(1, 2, 4, 3, 5, 6, 7), then
             input = List(List(1, 2, 4, 3), List(5, 6), List(), List(7))
    If output = List(1, 2, 3, 5, 6, 4, 7), then
             input = List(List(1, 2, 3), List(5, 6), List(), List(4, 7))
    If output = List(1, 2, 3, 5, 6, 7, 4), then
             input = List(List(1, 2, 3), List(5, 6), List(), List(7, 4))

### Map
Given `f` and its reverse function:

    val f = (x: Int) => x - (x%2)
    val fRev = (x: Int) => if(x % 2 == 0) List(x, x+1) else Nil

The following tests apply when mapping f on the input list:

    Original input: List(1, 2, 3, 4, 5)
    => output = List(0, 2, 2, 4, 4)
    If output = List(0, 4, 2, 4, 4),   input = List(1, 4, 3, 4, 5)     // 1 more
    If output = List(0, 2, 4, 4),      input = List(1, 2, 4, 5)        // and more
    If output = List(0, 2, 2, 2, 4, 4),input = List(1, 2, 3, 2, 4, 5)  // and more
    
### Filter
Given the filter `isEven` which checks if a number is even or not,

    Original input = List(1, 2, 3, 4, 8, 5)
    => output = List(2, 4, 8)
    if output = List(2, 8),       input = List(1, 2, 3, 8, 5)
    if output = List(4, 8),       input = List(1, 3, 4, 8, 5)
    if output = List(2, 4, 6, 8), input = List(1, 2, 3, 4, 6, 8, 5)
    if output = List(2, 6, 4, 8), input = List(1, 2, 3, 6, 4, 8, 5)

### FlatMap
Flatmap could be viewed as a composition between map and flatten, but we thought it could have its own reverse function.
Since flatMap takes a lambda `A => List[B]` in parameter, its reverse has to take a lambda `List[B] => List[A]`,
which returns all possible values of type `A` which exactly produce the input of type `List[B]`.

We tested our function on the following lambda:

    val f = (x: Int) => (x % 4) match {
      case 0 => List(x, x+1, x+2)
      case 1 => List(x-1, x)
      case 2 => List(x+1, x+2)
      case 3 => List(x-1, x, x+1)
    }

This awesome function hides the simple fact that:

    f(0) == List(0, 1, 2)
    f(1) == List(0, 1)
    f(2) == List(3, 4)
    f(3) == List(2, 3, 4)
    f(0) ++ f(2) == f(1) ++ f(3)
  
so that there can be ambiguity when reversing flatMap.
However, if the output is exactly the expected one, the input will be the original one, no matter how much ambiguity there is.

    Original input: Nil
    => output = Nil
    if output = List(0, 1, 2, 3, 4), input = List(1, 3)       // Also List(0, 2)
    
    Original input: List(0, 2)
    => output = List(0, 1, 2, 3, 4)
    If output = List(0, 1, 2, 3, 4, 0, 1)
             input = List(0, 2, 1)
    If output = List(0, 1, 2, 0, 1, 3, 4)
             input = List(0, 1, 2)
    If output = List(0, 1, 0, 1, 2, 3, 4)
             input = List(1, 0, 2)
    If output = List(3, 4)
             input = List(2)
    If output = List(0, 1, 0, 1, 2, 3, 4)
             input = List(2)

Now for a `flatMap` mimicking a filter, keeping only even numbers but dividing them by 2:

    Original input: List(1, 2, 3, 4, 5)
    => output = List(1, 2)
    If output = List(1, 3, 2)
             input =List(1, 2, 3, 6, 4, 5)
    If output = List(2)
             input = List(1, 2, 3, 5)

