# INCA

A tool to navigate answer-set programs using facets. 

## Prerequisites

```
Python (tested with python 2.7)
Clingo (tested with clingo 5.2)
```

Information about Clingo and how to download it is available [here](https://potassco.org/clingo/).\
Releases of python are available [here](https://www.python.org/downloads/).

## Running

In order to run INCA, clingo.(pyd / so) needs to be in the same directory of inca.py.\
The tool can be launched using the command

```
python inca.py -f <asp_program.lp>
```

## Commands

List of the tool's commands

```
Apply a nav. step using an inclusive facet                    ex: p(y1,y2)
                                               
Apply a nav. step using an exclusive facet                    ex: #not p(y1,y2)
                                          
Retract a specific facet                                      ex: #del p(y1,y2)
                                          
Show the consequences of removing certain facets              ex: #what p(y1,y2)
                                         
Calculate all minimal correction sets w.r.t. some facet       ex: #how p(y1,y2)
                                          
Retract all facets                                            delall
                                                     
List all applied facets                                       lk
                                                         
Display active / inactive facets                              show
                                                       
Terminate the program                                         exit
```

## Navigation Example

The following is an example of the faceted navigation of the graph coloring problem with 3 colors.

Input program

```
%Every node has exactly one color
{ color(X,C): col(C) } = 1 :- node(X).

%Connected nodes must have different colors	
:- edge(X,Y), color(X,C), color(Y,C).

%Nodes
node(1..6).

%Colors
col(r). col(g). col(b).

%Edges
edge(1,(2;6)).   edge(2,(1;3;4)).  edge(3,(2;4;5)).
edge(4,(2;3;5)). edge(5,(3;4;6)).  edge(6,(1;5)).
```

To apply a navigation step, a facet from the available one must be chosen, in our example we choose the color of node 2 to be green by typing `color(2,g).` \
This selection implies that node 5 must be green as well, therfore the user's confirmation is required. Afterwards three lists would be displayed

```
Unavailable Facets:
------------------

color(1,g)  color(2,b)  color(2,r)  color(3,g)  color(4,g)  color(5,b)  color(5,r)  color(6,g)  

not color(5,g)  not color(2,g)  


Available Facets:  
----------------

color(3,b)  color(4,b)  color(6,r)  color(1,r)  color(3,r)  color(4,r)

color(6,b)  color(1,b)  not color(3,b)  not color(4,b)  not color(6,r)

not color(1,r)  not color(3,r)  not color(4,r)  not color(6,b)  not color(1,b)  


Chosen Facets:  
-------------

color(5,g)  color(2,g)  
```

After applying `color(1,b).` and then `#not color(3,r).`, we reach the end of the navigation because there are no more facets to apply any additional steps.

Computing all minimal correction sets of the current program with respect to `#not color(4,r).` can be achieved via `#how #not color(4,r).`

```
Total number of correction sets = 2

To be able to select not color(4,r) you have to remove
	
	color(2,g)
or
	not color(3,r)
```

### Remarks

Input programs must not have the `#show` command because it creates a problem in desplaying the correction sets.\
Removing multiple facets, as well as the inquiry about the consequences of removing multiple facets is possible; facets must be seperated by "/".